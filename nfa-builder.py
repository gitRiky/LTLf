import itertools
import sys
import codecs
from LTLf_translator import remove_spaces, remove_useless_parenthesis, populate_subformula, sigma, has_less_priority

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

AND_STATE_SEPARATOR = " - "
OR_STATE_SEPARATOR = ", "

OPERATORS = [AND, OR, NEXT, WEAK_NEXT, UNTIL, GLOBALLY, EVENTUALLY, WEAK_UNTIL]

alphabet = []
cl = {}
proposition_combination = []
last_pointer = []


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


# Used for obtaining all the possible combinations of fluents
def create_proposition_combination(result):
    for i in range(len(alphabet)+1):
        comb = itertools.combinations(alphabet, i)
        for tup in comb:
            result.append(tup)


# This is the real nfa builder method: for each fluents combination, it applies the delta for each state until
# no more states are added. It returns the set of states s and the transition function
def ltlf_2_nfa(propositions, nnf):
    exist_true_state = False
    s0 = nnf
    sf = FALSE
    s_before = {sf}
    s = {s0, sf}
    transition_function = {}
    while s_before != s:
        diff = s.difference(s_before)
        print(diff)
        s_before = s.copy()
        for state in diff:
            if state != TRUE and state != FALSE:
                for prop in propositions:
                    new_state = delta(state, prop)
                    if new_state == TRUE and LAST not in prop:
                        exist_true_state = True
                    print("New state: " + new_state)
                    tup = (state, prop)
                    if OR_STATE_SEPARATOR in new_state:               # is an or of states
                        split = new_state.split(OR_STATE_SEPARATOR)
                        for elem in split:
                            if elem not in s:
                                s.add(elem)
                    elif new_state not in s:
                        s.add(new_state)
                    transition_function[tup] = new_state
        print(s)
        print(s_before)
    for key in transition_function.keys():
        state = key[0]
        fluents = key[1]
        print("State \t\t" + str(state))
        print("Fluents \t" + str(fluents))
        print("New State \t" + transition_function[key] + "\n")
    print(s)
    return s, transition_function, exist_true_state


def remove_last(transition_function):
    exist_ended_state = False
    new_transition_function = {}
    for key in transition_function.keys():
        fluents = key[1]
        if LAST not in fluents:
            if key in new_transition_function.keys() and transition_function[key] != TRUE:
                new_transition_function[key] = new_transition_function[key] + \
                                               OR_STATE_SEPARATOR + transition_function[key]
            else:
                new_transition_function[key] = transition_function[key]
        elif transition_function[key] == TRUE:
            exist_ended_state = True
            new_tuple = ()
            state = key[0]
            for elem in fluents:
                if elem != LAST:
                    new_tuple += (elem,)
            new_key = (state, new_tuple)
            if transition_function[new_key] == TRUE:
                new_transition_function[new_key] = TRUE
            elif new_key in new_transition_function.keys():
                new_transition_function[new_key] = new_transition_function[new_key] + OR_STATE_SEPARATOR + ENDED
            else:
                new_transition_function[new_key] = ENDED
    return new_transition_function, exist_ended_state


def print_nfa(s0, s, transition_function):
    alphabet.remove(LAST)
    print("\n\n----------------------------------------------\n")
    print("Alphabet: " + str(alphabet) + "\n")

    print("States: " + str(s) + "\n")
    print("Initial state: " + s0 + "\n")

    f = set([])
    if TRUE in s:
        f.add(TRUE)
    if ENDED in s:
        f.add(ENDED)
    print("Final states: " + str(f) + "\n")
    print("Transition function:")
    for key in transition_function.keys():
        state = key[0]
        fluents = key[1]
        print("\tState: " + state)
        print("\tFluents: " + str(fluents))
        print("\tNew state: " + transition_function[key] + "\n")
    print("\n----------------------------------------------\n")


def run_nfa(sequence, s0, transition_function):
    current_state = s0
    for elem in sequence:
        if OR_STATE_SEPARATOR in current_state:
            split = current_state.split(OR_STATE_SEPARATOR)
            new_state = ""
            for state in split:
                if state != ENDED:
                    n_state = transition_function[(state, elem)]
                    if n_state == TRUE:
                        new_state = TRUE
                        break
                    if n_state != FALSE:
                        if len(new_state) < 1:
                            new_state += n_state
                        else:
                            new_state += OR_STATE_SEPARATOR + n_state
            if new_state == "":
                new_state = FALSE
        else:
            new_state = transition_function[(current_state, elem)]
        print("State: " + current_state + "\nFluents: " + str(elem) + "\nNew state: " + new_state + "\n")
        if new_state == TRUE:
            return True
        if new_state == FALSE:
            return False
        current_state = new_state
    if ENDED in current_state:
        return True
    return False


def main():
    if len(sys.argv) < 2:
        print("Correct usage: python .\\nfa-builder.py alphabet_file")
        exit(-1)
    alphabet_file = sys.argv[1]
    ltlf_formula = input("Insert the LTLf formula\n")
    nnf = convert_to_nnf(ltlf_formula)
    print(nnf)

    # This method is used for building the dictionary of subformulas (i.e. the cl of the AFW)
    # The dictionary cl will be used in the delta function for understanding what kind of formula is it and what
    # recursive rule it has to follow
    sigma(nnf, cl)
    print("CL\n" + str(cl))
    with codecs.open(alphabet_file, 'r') as file_handle:
        for line in file_handle:
            line = line.replace("\n", "")
            alphabet.append(line)
    alphabet.append(LAST)
    create_proposition_combination(proposition_combination)
    s, transition_function, exist_true_state = ltlf_2_nfa(proposition_combination, nnf)
    new_transition_function, exist_ended_state = remove_last(transition_function)
    if not exist_true_state:
        s.remove(TRUE)
    if exist_ended_state:
        s.add(ENDED)
    print_nfa(nnf, s, new_transition_function)
    done = False
    while not done:
        response = input("Do you want to provide a sequence of fluents for simulating a run? (y, n)\n")
        while response not in ["y", "n"]:
            print("Not valid response. Type 'y' if you want to continue or 'n' if you want to exit")
            response = input()
        if response == "y":
            sequence = []
            sequence_file_name = input("Insert the name of the file containing the sequence of fluents\n")
            with codecs.open(sequence_file_name, 'r') as file_handle:
                for line in file_handle:
                    line = line.replace("\n", "")
                    if line == "":
                        sequence.append(())
                    else:
                        split = line.split(",")
                        tuple_res = ()
                        for elem in split:
                            tuple_res += (elem,)
                        sequence.append(tuple_res)
            print("\n-----------------------------------------------------------\n")
            final_state_reached = run_nfa(sequence, nnf, new_transition_function)
            if final_state_reached:
                print("The trace satisfies the LTLf formula\n")
            else:
                print("The trace does not satisfy the LTLf formula\n")
        else:
            done = True


main()
