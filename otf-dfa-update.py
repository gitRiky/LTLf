from utility import *
from LTLf_translator import sigma
import sys
import codecs

CL_FILE_PATH = "/home/riccardo/nfa-builder/cl.txt"
LOG_FILE_PATH = "/home/riccardo/nfa-builder/log.txt"
NEXT_STATE_FILE_PATH = "/home/riccardo/fs/workspace/nextState.txt"
cl = {}


def run_on_the_fly_dfa(s0, trace, procedure=False):
    current_state = s0
    for fluents in trace:
        # I add to the already true fluents also the last fluent. By definition, if the resulting state will be true,
        # then it can reach the 'ended' state
        fluents_last = fluents + (LAST,)
        if current_state != ENDED:
            next_state = delta(current_state, fluents)
            if OR_STATE_SEPARATOR in next_state:
                split = next_state.split(OR_STATE_SEPARATOR)
                next_state = ""
                states_set = set([])
                for elem in split:
                    if AND_STATE_SEPARATOR in elem:
                        elem = sort_and_state(elem)
                    if elem not in states_set:
                        states_set.add(elem)
                        if len(next_state) < 1:
                            next_state = elem
                        else:
                            next_state += OR_STATE_SEPARATOR + elem
            if next_state != TRUE and delta(current_state, fluents_last) == TRUE:
                if next_state != "":
                    next_state += OR_STATE_SEPARATOR + ENDED
                else:
                    next_state = ENDED
            # print_state(current_state, fluents, next_state)
        if procedure:
            return next_state
        if next_state == TRUE:
            return True
        if next_state == FALSE:
            return False
        current_state = next_state
    if ENDED in current_state:
        return True
    return False


def delta(state, action_effect):
    # The or of states is managed in this method. Typically in a deterministic automaton we have states of kind
    # [q1,q2], then we have to understand where with a specific symbol will go q1 and where will go q2.
    # This if applies the delta to each state and put the states in a result set, that will be returned as a string.
    # E.g. q1-> q2,q3, q2->q2 (with 'a' for example). The result set will be {q2,q3} and the returned string will be
    # q2, q3.
    if state == TRUE:
        return TRUE
    if OR_STATE_SEPARATOR in state:
        states_set = set([])
        for elem in state.split(OR_STATE_SEPARATOR):
            if elem != ENDED:
                d = delta(elem, action_effect)
                if d == TRUE:                       # For the angelic non-determinism
                    return TRUE
                if d != FALSE:
                    # It is used for avoiding duplicates, e.g. [q1, q2, q1] -> [q1, q2]
                    if OR_STATE_SEPARATOR in d:
                        for el in d.split(OR_STATE_SEPARATOR):
                            if el not in states_set:
                                states_set.add(el)
                    elif d not in states_set:
                        states_set.add(d)
        if len(states_set) < 1:
            return FALSE
        else:
            new_state = ""
            first = True
            for s in states_set:
                if first:
                    first = False
                    new_state += s
                else:
                    new_state += OR_STATE_SEPARATOR + s
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


def construct_fluents_tuple(state):
    # only the fluents contained in the goal are needed!!! Pre-processing c++ side
    fluents_tuple = ()
    for fluent in state.split(";"):
        fluent = fluent.replace(" ", "").replace("(", "{").replace(")", "}")
        fluents_tuple += (fluent,)
    return fluents_tuple


def update_state(domain_state, automaton_state):
    next_automaton_state = run_on_the_fly_dfa(automaton_state, [domain_state], True)
    return next_automaton_state


def read_cl():
    with codecs.open(CL_FILE_PATH, "r") as file_handle:
        for line in file_handle:
            line = line.replace("\n", "")
            split = line.split("\t")
            cl[split[0]] = split[1]


def main():
    domain_state = sys.argv[1]
    automaton_state = sys.argv[2]
    log_string = ""
    domain_state = construct_fluents_tuple(domain_state)
    log_string += "Domain state:\n" + str(domain_state) + "\n"
    automaton_state = automaton_state.replace("*", " ")
    log_string += "Automaton state:\n" + str(automaton_state) + "\n"
    read_cl()
    next_state = update_state(domain_state, automaton_state)
    log_string += "Next state:\n" + str(next_state) + "\n-------------------------------------------------\n"
    with codecs.open(NEXT_STATE_FILE_PATH, "w") as file_handle:
        next_state = "[" + next_state.replace(" ", "*") + "]"
        file_handle.write(next_state)
    with codecs.open(LOG_FILE_PATH, "a") as file_handle:
        file_handle.write(log_string)
main()
