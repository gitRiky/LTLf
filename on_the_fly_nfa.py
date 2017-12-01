import codecs
from utility import *


cl = {}

# If we want to see the single state transition, it has to be set to True. Otherwise to false.
# i.e. we are in both q1 and q2. We know that with 'a' from q1 we'll go to q3 and from q2 to q4.
# With the parameter set to false, we will see
#       State: q1,q2
#       Fluent.....
#       New State = {q3,q4}
# With the parameter set to true, we will se also the single transition, i.e. q1-> q3 and q2-> q4
PRINT_SINGLE_STATE_TRANSITION = False


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
            return compute_tf_and(result_set)
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
        if d1 == d2:
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
        if d1 == d2:
            return d1
        return d1 + OR_STATE_SEPARATOR + d2


def print_state(current_state, fluents, new_state, nd=False):
    if nd:
        if type(new_state) == list:
            n_state = new_state[0]
            for elem in new_state[1:]:
                n_state += OR_STATE_SEPARATOR + elem
        else:
            n_state = new_state
        print("**Single-state transition**")
        print("State: " + current_state)
        print("Fluents: " + str(fluents))
        print("New states: {" + n_state + "}\n")
    else:
        print("\tStates: {" + current_state + "}")
        print("\tFluents: " + str(fluents))
        print("\tNew states: {" + new_state + "}\n")


def sort_and_state(elem):
    and_state_list = sorted(elem.split(AND_STATE_SEPARATOR))
    and_state = ""
    for sub_elem in and_state_list:
        if len(and_state) < 1:
            and_state = sub_elem
        else:
            and_state += AND_STATE_SEPARATOR + sub_elem
    return and_state


def run_on_the_fly_nfa(s0, trace):
    current_state = s0
    for fluents in trace:               # For each fluent in the trace
        fluents_last = fluents + (LAST,)
        if OR_STATE_SEPARATOR in current_state:
            next_states = set([])
            next_state = ""
            split = current_state.split(OR_STATE_SEPARATOR)
            for c_state in split:             # We apply the delta to each state in the current state (or)
                if c_state != ENDED:
                    n_state = delta(c_state, fluents)
                    if n_state == TRUE:
                        next_state = TRUE
                        if PRINT_SINGLE_STATE_TRANSITION:
                            print_state(c_state, fluents, TRUE, True)
                        break
                    if delta(c_state, fluents_last) == TRUE:          # Add ended to the set of states
                        n_state += OR_STATE_SEPARATOR + ENDED
                    if OR_STATE_SEPARATOR in n_state:           # The new state is an or of states
                        new_state_split = n_state.split(OR_STATE_SEPARATOR)

                        # We insert the single new state not already present in next states
                        for s in new_state_split:
                            if s != FALSE:
                                if AND_STATE_SEPARATOR in s:
                                    s = sort_and_state(s)
                                if s not in next_states:
                                    next_states.add(s)
                                    if len(next_states) == 1:
                                        next_state = s
                                    else:
                                        next_state += OR_STATE_SEPARATOR + s
                        if PRINT_SINGLE_STATE_TRANSITION:
                            print_state(c_state, fluents, new_state_split, True)
                    else:
                        if n_state != FALSE:
                            if AND_STATE_SEPARATOR in n_state:
                                n_state = sort_and_state(n_state)
                            if n_state not in next_states:
                                next_states.add(n_state)
                                if len(next_states) == 1:
                                    next_state = n_state
                                else:
                                    next_state += OR_STATE_SEPARATOR + n_state
                        if PRINT_SINGLE_STATE_TRANSITION:
                            print_state(c_state, fluents, n_state, True)
            if len(next_states) < 1 and next_state != TRUE:
                next_state = FALSE
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

    # This method is used for building the dictionary of subformulas (i.e. the cl of the AFW)
    # The dictionary cl will be used in the delta function for understanding what kind of formula is it and what
    # recursive rule it has to follow
    sigma(nnf, cl)
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
