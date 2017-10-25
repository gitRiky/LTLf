import itertools
import codecs
from utility import *

alphabet = []
cl = {}
proposition_combination = []


def from_fzsets_to_set(s):
    new_set = set([])
    for states_set in s:
        state = ""
        for elem in states_set:
            if len(state) < 1:
                state += elem
            else:
                state += OR_STATE_SEPARATOR + elem
        new_set.add(state)
    return new_set


def delta(state, action_effect):
    if OR_STATE_SEPARATOR in state:
        states_set = set([])
        new_state = ""
        for elem in state.split(OR_STATE_SEPARATOR):
            if elem != ENDED:
                d = delta(elem, action_effect)
                if d == TRUE:                       # For the angelic non-determinism
                    return TRUE
                if d != FALSE:
                    states_set.add(d)
                    if len(states_set) == 1:
                        new_state = d
                    else:
                        new_state += OR_STATE_SEPARATOR + d
        if len(states_set) < 1:
            return FALSE
        else:
            return new_state
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


# Used for obtaining all the possible combinations of fluents
def create_proposition_combination(result):
    for i in range(len(alphabet)+1):
        comb = itertools.combinations(alphabet, i)
        for tup in comb:
            result.append(tup)


# This is the core method. s represents a set of sets (frozenset because it is hashable).
# It applies the delta function to each state in the difference between Sn and Sn-1, for each combination of fluents.
# It obtains the transition function value that is stored in a dictionary (<key-value>)
# of kind <(state),(fluents)-new_state>. If the new state is not already in Sn, it adds it. If the state is final,
# i.e. ended is in the state or the state is equal to false, then it adds it to Sf.
# In the end, the sets of frozen sets S and Sf are translated into simple set of states.
def ltlf_2_dfa(propositions, nnf):
    s0 = frozenset([nnf])
    sf = set([])
    s_before = set([])
    s = {s0}
    transition_function = {}
    first = True
    while s_before != s:                    # Until we stop adding states
        if first:
            diff = s.copy()
            first = False
        else:
            diff = s.difference(s_before)
        s_before = s.copy()
        for f_set in diff:        # For each frozenset in Sn - Sn-1
            state = ""
            for st in f_set:      # Create a string with all the states of the frozen set, called state
                if len(state) < 1:
                    state = st
                else:
                    state += OR_STATE_SEPARATOR + st
            if state != TRUE and state != FALSE and state != ENDED:
                for prop in propositions:       # For each possible combination of fluents, apply the delta to state
                    last_fluent = prop + (LAST,)
                    new_state = delta(state, prop)
                    if new_state != TRUE and delta(state, last_fluent) == TRUE:
                        # If fluents + last from state returns true, then we must add ended to the new_state
                        new_state += OR_STATE_SEPARATOR + ENDED
                    if OR_STATE_SEPARATOR in new_state:
                        split = new_state.split(OR_STATE_SEPARATOR)
                        state_list = []
                        for elem in split:
                            if AND_STATE_SEPARATOR in elem:
                                and_state = sort_and_state(elem)
                                state_list.append(and_state)
                            else:
                                state_list.append(elem)
                    elif AND_STATE_SEPARATOR in new_state:
                        new_state = sort_and_state(new_state)
                        state_list = [new_state]
                    else:
                        state_list = [new_state]
                    state_set = frozenset(sorted(state_list))    # Here we transform a list of states into a frozenset
                    if state_set not in s:
                        s.add(state_set)
                    if ENDED in state_set and state_set not in sf:
                        sf.add(state_set)
                    if TRUE in state_set and state_set not in sf:
                        sf.add(state_set)
                    tup = (state, prop)             # This is the key of our transition function dictionary
                    new_state = ""
                    for elem in state_set:
                        if len(new_state) < 1:
                            new_state = elem
                        else:
                            new_state += OR_STATE_SEPARATOR + elem
                    transition_function[tup] = new_state
    set_s = from_fzsets_to_set(s)
    set_sf = from_fzsets_to_set(sf)
    return set_s, transition_function, set_sf


def print_dfa(s0, s, transition_function, sf):
    print("\n\n----------------------------------------------\n")
    print("Alphabet: " + str(alphabet) + "\n")

    states = "States: {"
    first = True
    for state in s:
        if first:
            first = False
            states += "[" + state + "]"
        else:
            states += ",\n\t[" + state + "]"
    print(states + "}\n")

    print("Initial state: [" + s0 + "]\n")

    f_states = "Final states: {"
    first = True
    for state in sf:
        if first:
            first = False
            f_states += "[" + state + "]"
        else:
            f_states += ",\n\t       [" + state + "]"
    print(f_states + "}\n")

    print("Transition function:")
    for key in transition_function.keys():
        state = key[0]
        fluents = key[1]
        print("\tState: [" + state + "]")
        fluents_to_print = ""
        for elem in fluents:
            if len(fluents_to_print) < 1:
                fluents_to_print = str(elem)
            else:
                fluents_to_print += " or " + str(elem)
        print("\tFluents: " + fluents_to_print)
        print("\tNew state: [" + transition_function[key] + "]\n")
    print("\n----------------------------------------------\n")


def run_dfa(sequence, s0, transition_function, sf):
    current_state = s0
    for elem in sequence:
        new_state = transition_function[(current_state, elem)]
        print("State: [" + current_state + "]\nFluents: " + str(elem) + "\nNew state: [" + new_state + "]\n")
        if new_state == TRUE:
            return True
        if new_state == FALSE:
            return False
        current_state = new_state
    if current_state in sf:
        return True
    return False


def verify_containment(tuple1, tuple2):
    contained = False
    for elem1 in tuple1:
        contained = False
        for elem2 in tuple2:
            if elem1 == elem2:
                contained = True
                break
        if not contained:
            return False
    return contained


# It must return a tuple representing the or of fluents
def simplify_dnf(dnf):
    new_clauses = dnf.copy()
    auxiliary_set = dnf.copy()
    for clause in dnf:
        for clause_to_compare in auxiliary_set:
            if clause != clause_to_compare:
                if len(clause) < len(clause_to_compare):
                    if verify_containment(clause, clause_to_compare):
                        new_clauses.discard(clause_to_compare)
                elif len(clause) > len(clause_to_compare):
                    if verify_containment(clause_to_compare, clause):
                        new_clauses.discard(clause)
    print("New clauses: " + str(new_clauses))
    compact_tuple = ()
    for elem in new_clauses:
        compact_tuple += (elem,)
    print(str(compact_tuple))
    return compact_tuple


# # It must return a tuple representing the or of fluents
# def simplify_dnf(dnf):
#     no_more_simplification = False
#     new_clauses = dnf.copy()
#     while not no_more_simplification:
#         auxiliary_set = dnf.copy()
#         for clause in dnf:
#             for clause_to_compare in auxiliary_set:
#                 if clause != clause_to_compare:
#                     if len(clause) < len(clause_to_compare):
#                         if verify_containment(clause, clause_to_compare):
#                             new_clauses.discard(clause_to_compare)
#                     elif len(clause) > len(clause_to_compare):
#                         if verify_containment(clause_to_compare, clause):
#                             new_clauses.discard(clause)
#         print("New clauses: " + str(new_clauses))
#         if new_clauses.difference(dnf) == set([]):
#             no_more_simplification = True
#         else:
#             dnf = new_clauses.copy()
#     compact_tuple = ()
#     for elem in new_clauses:
#         compact_tuple += (elem,)
#     print(str(compact_tuple))
#     return compact_tuple


def compact_fluents_notation(t_function, s):
    compact_t_function = {}
    same_state_dict = {}
    for state in s:
        if state not in [TRUE, ENDED, FALSE]:
            for pointer1 in range(0, len(proposition_combination)-1):
                key1 = (state, proposition_combination[pointer1])
                next_state = t_function[key1]
                dict_key = (state, next_state)
                if dict_key not in same_state_dict.keys():
                    same_state_dict[dict_key] = {tuple(key1[1])}
                for pointer2 in range(pointer1+1, len(proposition_combination)):
                    key2 = (state, proposition_combination[pointer2])
                    if next_state == t_function[key2]:
                        old_set = same_state_dict[dict_key]
                        old_set.add(key2[1])
                        print("Old set: " + str(old_set))
                        same_state_dict[dict_key] = old_set
    print(str(same_state_dict))
    for key in same_state_dict.keys():
        state = key[0]
        next_state = key[1]
        compact_fluents = simplify_dnf(same_state_dict[key])
        compact_t_function[(state, compact_fluents)] = next_state
    return compact_t_function


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
    create_proposition_combination(proposition_combination)
    s, transition_function, sf = ltlf_2_dfa(proposition_combination, nnf)
    compact_transition_function = compact_fluents_notation(transition_function, s)
    print_dfa(nnf, s, compact_transition_function, sf)
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
            final_state_reached = run_dfa(sequence, nnf, transition_function, sf)
            if final_state_reached:
                print("The trace satisfies the LTLf formula\n")
            else:
                print("The trace does not satisfy the LTLf formula\n")
        else:
            done = True


main()
