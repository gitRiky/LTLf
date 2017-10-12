from LTLf_translator import sigma, remove_useless_parenthesis, remove_spaces, has_less_priority, populate_subformula


import sys
import codecs

FALSE = "false"
TRUE = "true"
LAST = "last"
ENDED = "ended"
LIT = "lit"
NOT = "not"
AND = "and"
OR = "or"
NEXT = "X"
WEAK_NEXT = "WX"
UNTIL = "U"
WEAK_UNTIL = "R"
GLOBALLY = "G"
EVENTUALLY = "F"

OPERATORS = [AND, OR, NEXT, WEAK_NEXT, UNTIL, GLOBALLY, EVENTUALLY, WEAK_UNTIL]

AND_STATE_SEPARATOR = " - "
OR_STATE_SEPARATOR = ", "


cl = {}

PRINT_SINGLE_STATE_TRANSITION = True


def find_alpha_beta(subformula, formula_type):
    split = subformula.replace("(", "( ").replace(")", " )").split()
    parenthesis = 0
    counter = 0
    pointer = [0, sys.maxsize]  # pointer = (position of the operator, number of parenthesis)
    for elem in split:
        if elem == "(":
            parenthesis += 1
        elif elem == ")":
            parenthesis -= 1
        elif elem == formula_type and parenthesis < pointer[1]:
            pointer = [counter, parenthesis]
        counter += 1
    alpha = remove_spaces(populate_subformula(split, 0, pointer[0]))
    beta = remove_spaces(populate_subformula(split, pointer[0] + 1, len(split)))
    if formula_type == UNTIL or formula_type == WEAK_UNTIL:
        alpha = alpha[1:len(alpha)-1]
        beta = beta[1:len(beta)-1]
    return alpha, beta


def find_alpha(formula_type, subformula):
    alpha = subformula[len(formula_type)+2:len(subformula)-1]
    return alpha


# This method linearly scans the formula with the goal of finding external negation.
# When it finds one, it calls an auxiliary recursive method put_neg_inside(subformula) which is used for putting
# the negation inside the subformula
def convert_to_nnf(ltlf_formula):
    split = ltlf_formula.replace("(", "( ").replace(")", " )").split()
    print(split)
    counter = 0
    parenthesis = 0
    found_not = False
    parse_subformula = False
    subformula = ""
    new_formula = ""
    operator = ""
    left_part = ""
    for elem in split:
        if found_not:
            found_not = False
            print("Not has been found")
            if elem in [NEXT, WEAK_NEXT, EVENTUALLY, GLOBALLY]:
                parse_subformula = True
                operator = elem
                continue
            elif elem == "(":
                print("Is subformula")
                parse_subformula = True
            else:       # literal
                left_part += NOT + " " + elem + " "
                continue
        if parse_subformula:
            if elem == "(":
                parenthesis += 1
            elif elem == ")":
                parenthesis -= 1
            subformula += elem + " "
            if parenthesis == 0:
                subformula = subformula[1:len(subformula)-2]
                if new_formula != "":
                    new_formula += " "
                if operator == NEXT or operator == WEAK_NEXT:
                    new_formula += left_part + NEXT + " (" + put_neg_inside(subformula) + ")"
                elif operator == EVENTUALLY:
                    new_formula += left_part + GLOBALLY + " (" + put_neg_inside(subformula) + ")"
                elif operator == GLOBALLY:
                    new_formula += left_part + EVENTUALLY + " (" + put_neg_inside(subformula) + ")"
                else:
                    new_formula += left_part + put_neg_inside(subformula)
                subformula = ""
                parse_subformula = False
                left_part = ""
        elif elem == "not":
            found_not = True
        else:
            left_part += elem + " "
        counter += 1
    if new_formula == "":
        new_formula = left_part
    else:
        new_formula += " " + left_part
    if new_formula[len(new_formula)-1] == " ":
        new_formula = new_formula[:len(new_formula)-1]
    return remove_spaces(new_formula)


# The number of recursive calls is linear w.r.t. the size of the subformula. A subformula is not processed twice
# i.e. linear number of recursive calls w.r.t. the formula itself (in the worst case of course)
def put_neg_inside(subformula):
    pointer = ["", sys.maxsize, 0]
    count = 0
    parenthesis = 0
    left_part = ""
    right_part = ""
    split = subformula.split()
    print(split)
    if len(split) >= 2:
        if split[0] == NOT and split[1] == "(":
            # NOT before parenthesis, return the formula without the not
            return subformula[5:]
    for elem in split:
        if elem in OPERATORS:
            if parenthesis < pointer[1]:
                left_part += pointer[0] + " " + right_part
                right_part = ""
                pointer = [elem, parenthesis, count]
                print("Pointer: ", pointer)
            elif (parenthesis <= pointer[1]) and (has_less_priority(elem, pointer[0])):
                left_part += pointer[0] + " " + right_part
                right_part = ""
                pointer = [elem, parenthesis, count]
                print("Pointer: ", pointer)
            else:
                right_part += elem + " "
        else:
            right_part += elem + " "
            if elem == "(":
                parenthesis += 1
            if elem == ")":
                parenthesis -= 1
        count += 1
    left_part = remove_useless_parenthesis(left_part)
    right_part = remove_useless_parenthesis(right_part)
    operator = pointer[0]
    if operator == "":
        if split[0] == NOT:
            return split[1]
        else:
            return NOT + " " + split[0]
    if operator == AND:
        return put_neg_inside(left_part) + " or " + put_neg_inside(right_part)
    if operator == OR:
        return put_neg_inside(left_part) + " and " + put_neg_inside(right_part)
    elif operator == NEXT:
        return NEXT + " (" + put_neg_inside(right_part[1:len(right_part)-1]) + ")"
    elif operator == WEAK_NEXT:
        return NEXT + " (" + put_neg_inside(right_part[1:len(right_part)-1]) + ")"
    elif operator == EVENTUALLY:
        return GLOBALLY + " (" + put_neg_inside(right_part[1:len(right_part)-1]) + ")"
    elif operator == GLOBALLY:
        return EVENTUALLY + " (" + put_neg_inside(right_part[1:len(right_part) - 1]) + ")"


def delta(state, action_effect):
    if AND_STATE_SEPARATOR in state:
        result_set = []
        split = state.split(AND_STATE_SEPARATOR)

        # This portion of code is used in order to implement the 'and' between n delta functions
        for elem in split:
            d = delta(elem, action_effect)
            if d == FALSE:
                return FALSE
            if d != TRUE:
                append = True
                for r in result_set:
                    if d == r or d + AND_STATE_SEPARATOR in r:
                        append = False
                if append:
                    result_set.append(d)
        if len(result_set) < 1:
            return TRUE
        else:
            return_value = str(result_set[0])
            for i in range(1, len(result_set)):
                append = True
                for j in range(len(result_set)):
                    if i != j:
                        to_put = result_set[i]
                        if to_put == result_set[j] or to_put + AND_STATE_SEPARATOR in result_set[j]:
                            append = False
                            break
                if append:
                    return_value += AND_STATE_SEPARATOR + elem
            return return_value
    formula_type = cl[state]
    if formula_type == LIT:
        split = state.replace(" ", ",").replace("not,", "not ").split()
        if len(split) > 1:              # negative literal
            if split[1] not in action_effect:
                return TRUE
            else:
                return FALSE
        else:
            if state in action_effect:
                return TRUE
            else:
                return FALSE
    elif formula_type == EVENTUALLY:
        alpha = find_alpha(formula_type, state)
        d1 = delta(alpha, action_effect)
        if d1 == TRUE:
            return TRUE
        else:
            beta = NEXT + " (" + state + ")"
            d2 = delta(beta, action_effect)
            if d2 == TRUE:
                return TRUE
            if d1 == FALSE and d2 == FALSE:
                return FALSE
            if d1 == FALSE:
                return d2
            if d2 == FALSE:
                return d1
            return d1 + OR_STATE_SEPARATOR + d2
    elif formula_type == NEXT:
        if LAST in action_effect:
            return FALSE
        else:
            return find_alpha(formula_type, state)
    elif formula_type == WEAK_NEXT:
        if LAST in action_effect:
            return TRUE
        else:
            return find_alpha(formula_type, state)
    elif formula_type == GLOBALLY:
        alpha = find_alpha(formula_type, state)
        d1 = delta(alpha, action_effect)
        if d1 == FALSE:
            return FALSE
        d2 = delta(WEAK_NEXT + " (" + state + ")", action_effect)
        if d2 == FALSE:
            return FALSE
        if d1 == TRUE and d2 == TRUE:
            return TRUE
        if d1 == TRUE:
            return d2
        if d2 == TRUE:
            return d1
        if OR_STATE_SEPARATOR in d1:
            split = d1.split(OR_STATE_SEPARATOR)
            return_value = split[0] + AND_STATE_SEPARATOR + d2
            for state in split[1:]:
                return_value += OR_STATE_SEPARATOR + state + AND_STATE_SEPARATOR + d2
            return return_value
        else:
            return d1 + AND_STATE_SEPARATOR + d2
    elif formula_type == UNTIL:
        alpha, beta = find_alpha_beta(state, formula_type)
        d1 = delta(beta, action_effect)
        if d1 == TRUE:
            return TRUE
        d2 = delta(alpha, action_effect)
        if d2 == FALSE:
            return FALSE
        d3 = delta(NEXT + " (" + state + ")", action_effect)
        if d3 == FALSE:
            return FALSE
        if d2 == TRUE and d3 == TRUE:
            return TRUE
        if d1 == FALSE:
            if d2 == TRUE:
                return d3
            if d3 == TRUE:
                return d2
            else:
                return d2 + AND_STATE_SEPARATOR + d3
        if d2 == TRUE:
            return d1 + OR_STATE_SEPARATOR + d3
        if d3 == TRUE:
            return d1 + OR_STATE_SEPARATOR + d2
        return d2 + AND_STATE_SEPARATOR + d3
    elif formula_type == WEAK_UNTIL:
        alpha, beta = find_alpha_beta(state, formula_type)
        d1 = delta(beta, action_effect)
        if d1 == FALSE:
            return FALSE
        d2 = delta(alpha, action_effect)
        d3 = delta(WEAK_NEXT + " (" + state + ")", action_effect)
        if d2 == TRUE and d1 == TRUE:
            return TRUE
        if d3 == TRUE and d1 == TRUE:
            return TRUE
        if d2 == FALSE and d3 == FALSE:
            return FALSE
        if d1 == TRUE:
            if d2 == FALSE:
                return d3
            if d3 == FALSE:
                return d2
        else:
            if d2 == FALSE:
                return d1 + AND_STATE_SEPARATOR + d3
            if d3 == FALSE:
                return d1 + AND_STATE_SEPARATOR + d2
        return d1 + AND_STATE_SEPARATOR + d2 + OR_STATE_SEPARATOR + d1 + AND_STATE_SEPARATOR + d3
    elif formula_type == AND:
        alpha, beta = find_alpha_beta(state, formula_type)
        d1 = delta(alpha, action_effect)
        if d1 == FALSE:
            return FALSE
        d2 = delta(beta, action_effect)
        if d2 == FALSE:
            return FALSE
        if d1 == TRUE and d2 == TRUE:
            return TRUE
        if d1 == TRUE:
            return d2
        if d2 == TRUE:
            return d1
        return d1 + AND_STATE_SEPARATOR + d2
    elif formula_type == OR:
        alpha, beta = find_alpha_beta(state, formula_type)
        d1 = delta(alpha, action_effect)
        if d1 == TRUE:
            return TRUE
        d2 = delta(beta, action_effect)
        if d2 == TRUE:
            return TRUE
        if d1 == FALSE and d2 == FALSE:
            return FALSE
        if d1 == FALSE:
            return d2
        if d2 == FALSE:
            return d1
        return d1 + OR_STATE_SEPARATOR + d2


def print_state(current_state, fluents, new_state, nd=False):
    if nd:
        print("**Single-state transition**")
        print("State: " + current_state)
        print("Fluents: " + str(fluents))
        print("New state: " + str(new_state) + "\n")
    else:
        print("\tState: " + current_state)
        print("\tFluents: " + str(fluents))
        print("\tNew state: " + new_state + "\n")


def run_on_the_fly_nfa(s0, trace):
    current_state = s0
    for fluents in trace:
        fluents_last = fluents + (LAST,)
        if OR_STATE_SEPARATOR in current_state:
            next_states = set([])
            split = current_state.split(OR_STATE_SEPARATOR)
            for state in split:
                if state != ENDED:
                    n_state = delta(state, fluents)
                    if n_state == TRUE:
                        next_states = {TRUE}
                        if PRINT_SINGLE_STATE_TRANSITION:
                            print_state(state, fluents, TRUE, True)
                        break
                    if OR_STATE_SEPARATOR in n_state:
                        new_state_split = n_state.split(OR_STATE_SEPARATOR)
                        for s in new_state_split:
                            if s != FALSE:
                                if s not in next_states:
                                    next_states.add(s)
                                if delta(state, fluents_last) == TRUE:
                                    if ENDED not in next_states:
                                        next_states.add(ENDED)
                                    s += OR_STATE_SEPARATOR + ENDED
                        if PRINT_SINGLE_STATE_TRANSITION:
                            print_state(state, fluents, new_state_split, True)
                    else:
                        if n_state != FALSE:
                            if n_state not in next_states:
                                next_states.add(n_state)
                            if delta(state, fluents_last) == TRUE:
                                if ENDED not in next_states:
                                    next_states.add(ENDED)
                                n_state += OR_STATE_SEPARATOR + ENDED
                        if PRINT_SINGLE_STATE_TRANSITION:
                            print_state(state, fluents, n_state, True)
            if len(next_states) < 1:
                next_state = FALSE
            else:
                next_state = ""
                first = True
                for elem in next_states:
                    if first:
                        first = False
                        next_state = elem
                    else:
                        next_state += OR_STATE_SEPARATOR + elem
        else:
            next_state = delta(current_state, fluents)
            if next_state != TRUE and delta(current_state, fluents_last) == TRUE:
                if next_state != "":
                    next_state += OR_STATE_SEPARATOR + ENDED
                else:
                    next_state = ENDED
        print_state(current_state, fluents, next_state)
        if next_state == TRUE:
            return True
        if next_state == FALSE:
            return False
        current_state = next_state
    if ENDED in current_state:
        return True
    return False


def main():
    if len(sys.argv) < 2:
        print("Correct usage: python .\\nfa-builder.py trace_file")
        exit(-1)
    trace_file_name = sys.argv[1]
    ltlf_formula = input("Insert the LTLf formula\n")
    nnf = convert_to_nnf(ltlf_formula)
    print(nnf)

    # This method is used for building the dictionary of subformulas (i.e. the cl of the AFW)
    # The dictionary cl will be used in the delta function for understanding what kind of formula is it and what
    # recursive rule it has to follow
    sigma(nnf, cl)
    print(cl)
    trace = []
    with codecs.open(trace_file_name, 'r') as file_handle:
        for line in file_handle:
            line = line.replace("\n", "")
            split = line.split(",")
            tuple_res = ()
            for elem in split:
                tuple_res += (elem,)
            trace.append(tuple_res)
    print("\n------------------------------------------------------\n")
    final_state_reached = run_on_the_fly_nfa(nnf, trace)
    if final_state_reached:
        print("The trace satisfies the LTLf formula\n")
    else:
        print("The trace does not satisfy the LTLf formula\n")


main()
