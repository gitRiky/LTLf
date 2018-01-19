import itertools
import codecs
from utility import *

alphabet = []
cl = {}
proposition_combination = []
last_pointer = []


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
            # Auxiliary method for computing the and between delta, avoiding duplicates
            print("Problem in compute_tf")
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
        return d1 + OR_STATE_SEPARATOR + d2 + AND_STATE_SEPARATOR + d3
    elif formula_type == RELEASE:
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


# Used for obtaining all the possible combinations of fluents
def create_proposition_combination(result):
    for i in range(len(alphabet)+1):
        comb = itertools.combinations(alphabet, i)
        for tup in comb:
            result.append(tup)


def sort_and_state(elem):
    and_state_list = sorted(elem.split(AND_STATE_SEPARATOR))
    and_state = ""
    for sub_elem in and_state_list:
        if len(and_state) < 1:
            and_state = sub_elem
        else:
            and_state += AND_STATE_SEPARATOR + sub_elem
    return and_state


# This is the real nfa builder method: for each fluents combination, it applies the delta for each state until
# no more states are added. It returns the set of states s and the transition function
def ltlf_2_nfa(propositions, nnf):
    s0 = nnf
    s_before = set([])
    s = {s0}
    transition_function = {}
    first = True
    while s_before != s:  # Until we stop adding states
        if first:
            diff = s.copy()
            first = False
        else:
            diff = s.difference(s_before)

        s_before = s.copy()
        for state in diff:
            if state != TRUE and state != FALSE and state != ENDED:
                for prop in propositions:
                    new_state = delta(state, prop)
                    tup = (state, prop)
                    if OR_STATE_SEPARATOR in new_state:               # is an or of states
                        split = new_state.split(OR_STATE_SEPARATOR)
                        new_state = ""
                        for elem in split:
                            if AND_STATE_SEPARATOR in elem:
                                and_state = sort_and_state(elem)
                                if len(new_state) < 1:
                                    new_state = and_state
                                else:
                                    new_state += OR_STATE_SEPARATOR + and_state
                                if and_state not in s:
                                    s.add(and_state)
                            else:
                                if len(new_state) < 1:
                                    new_state = elem
                                else:
                                    new_state += OR_STATE_SEPARATOR + elem
                                if elem not in s:
                                    s.add(elem)
                    elif AND_STATE_SEPARATOR in new_state:
                        new_state = sort_and_state(new_state)
                        if new_state not in s:
                            s.add(new_state)
                    elif new_state not in s:
                        s.add(new_state)
                    transition_function[tup] = new_state
    return s, transition_function


# This method is used for removing the special proposition 'last' from the sequence of fluents
def remove_last(transition_function):
    exist_ended_state = False
    exist_false_state = False
    exist_true_state = False
    new_transition_function = {}
    for key in transition_function.keys():
        fluents = key[1]
        if LAST not in fluents:
            if transition_function[key] == FALSE:
                exist_false_state = True
            elif transition_function[key] == TRUE:
                exist_true_state = True
            # We copy the transition function value but we may have already the ended state, so if we have it
            # we add the new_state with the OR_STATE_SEPARATOR, otherwise not
            if key in new_transition_function.keys() and transition_function[key] != TRUE:
                new_transition_function[key] = new_transition_function[key] + \
                                               OR_STATE_SEPARATOR + transition_function[key]
                exist_ended_state = True
            else:
                new_transition_function[key] = transition_function[key]
        elif transition_function[key] == TRUE:
            # Here we have to add the ended state
            new_tuple = ()
            state = key[0]
            for elem in fluents:
                if elem != LAST:
                    new_tuple += (elem,)
            new_key = (state, new_tuple)
            if transition_function[new_key] == TRUE:
                new_transition_function[new_key] = TRUE
            elif new_key in new_transition_function.keys():
                # same stuff as above
                exist_ended_state = True
                new_transition_function[new_key] = new_transition_function[new_key] + OR_STATE_SEPARATOR + ENDED
            else:
                new_transition_function[new_key] = ENDED
                exist_ended_state = True
    return new_transition_function, exist_ended_state, exist_false_state, exist_true_state


def print_nfa(s0, s, transition_function):
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
        fluents_to_print = ""
        for elem in fluents:
            if len(elem) > 1:
                clause = "(" + str(elem[0])
                for e in elem[1:]:
                    clause += " and " + str(e)
                if fluents_to_print == "":
                    fluents_to_print += clause + ")"
                else:
                    fluents_to_print += " or " + clause + ")"
            else:
                if fluents_to_print == "":
                    fluents_to_print += elem[0]
                else:
                    fluents_to_print += " or " + elem[0]
        print("\tFluents: " + fluents_to_print)
        print("\tNew states: {" + transition_function[key] + "}\n")
    print("\n----------------------------------------------\n")


def run_nfa(sequence, s0, transition_function):
    current_state = s0
    for elem in sequence:
        if OR_STATE_SEPARATOR in current_state:
            split = current_state.split(OR_STATE_SEPARATOR)
            new_state = ""
            new_states = set([])
            for c_state in split:
                if c_state != ENDED:
                    n_state = transition_function[(c_state, elem)]
                    if n_state == TRUE:
                        new_state = TRUE
                        break
                    if n_state != FALSE:
                        if OR_STATE_SEPARATOR in n_state:
                            for ns in n_state.split(OR_STATE_SEPARATOR):
                                if ns not in new_states:
                                    new_states.add(ns)
                                    if len(new_states) == 1:
                                        new_state = ns
                                    else:
                                        new_state += OR_STATE_SEPARATOR + ns
                        elif n_state not in new_states:
                            new_states.add(n_state)
                            if len(new_states) == 1:
                                new_state = n_state
                            else:
                                new_state += OR_STATE_SEPARATOR + n_state
            if new_state == "":
                new_state = FALSE
        else:
            new_state = transition_function[(current_state, elem)]
        print("States: {" + current_state + "}\nFluents: " + str(elem) + "\nNew states: {" + new_state + "}\n")
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

    # This method is used for building the dictionary of subformulas (i.e. the cl of the AFW)
    # The dictionary cl will be used in the delta function for understanding what kind of formula is it and what
    # recursive rule it has to follow
    sigma(nnf, cl)
    with codecs.open(alphabet_file, 'r') as file_handle:
        for line in file_handle:
            line = line.replace("\n", "")
            alphabet.append(line)
    alphabet.append(LAST)
    create_proposition_combination(proposition_combination)
    s, transition_function = ltlf_2_nfa(proposition_combination, nnf)
    new_transition_function, exist_ended_state, exist_false_state, exist_true_state = remove_last(transition_function)
    prop_without_last = []
    for prop in proposition_combination:
        if LAST not in prop:
            prop_without_last.append(prop)
    alphabet.remove(LAST)
    compact_transition_function = compact_fluents_notation(new_transition_function, s,
                                                           alphabet, prop_without_last)
    if not exist_true_state and TRUE in s:
        s.remove(TRUE)
    if exist_ended_state:
        s.add(ENDED)
    if not exist_false_state and FALSE in s:
        s.remove(FALSE)
    print_nfa(nnf, s, compact_transition_function)
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
