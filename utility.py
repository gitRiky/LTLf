import sys

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
RELEASE = "R"
GLOBALLY = "G"
EVENTUALLY = "F"

AND_STATE_SEPARATOR = " - "
OR_STATE_SEPARATOR = ", "

OPERATORS = [AND, OR, NEXT, WEAK_NEXT, UNTIL, GLOBALLY, EVENTUALLY, RELEASE]


def remove_spaces(form):
    form = form.replace("( ", "(").replace(" )", ")")
    return form


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
    if formula_type == UNTIL or formula_type == RELEASE:
        alpha = alpha[1:len(alpha)-1]
        beta = beta[1:len(beta)-1]
    return alpha, beta


def find_alpha(formula_type, subformula):
    alpha = subformula[len(formula_type)+2:len(subformula)-1]
    return alpha


def populate_subformula(split, start, end):
    subformula = ""
    first = True
    for elem in split[start:end]:
        if first:
            first = False
        else:
            subformula += " "
        subformula += elem
    subformula = remove_useless_parenthesis(subformula)
    subformula = remove_spaces(subformula)
    return subformula


def remove_useless_parenthesis(ltlf_formula):
    par = 0
    for char in ltlf_formula:
        if char == "(":
            par += 1
        elif char == ")":
            par -= 1
    if par > 0:
        ltlf_formula = ltlf_formula[par*2:]
    elif par < 0:
        ltlf_formula = ltlf_formula[:par*2]
    return ltlf_formula


# The number of recursive calls is linear w.r.t. the size of the subformula. A subformula is not processed twice
# i.e. linear number of recursive calls w.r.t. the formula itself (in the worst case of course)
def put_neg_inside(subformula):
    pointer = ["", sys.maxsize, 0]
    count = 0
    parenthesis = 0
    left_part = ""
    right_part = ""
    split = subformula.split()
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
            elif (parenthesis <= pointer[1]) and (has_less_priority(elem, pointer[0])):
                left_part += pointer[0] + " " + right_part
                right_part = ""
                pointer = [elem, parenthesis, count]
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
            if elem in [NEXT, WEAK_NEXT, EVENTUALLY, GLOBALLY]:
                parse_subformula = True
                operator = elem
                continue
            elif elem == "(":
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


def sigma(ltlf_formula, cl, literal=False):
    if remove_spaces(ltlf_formula) in cl.keys():                         # formula already in CL
        return
    if ltlf_formula[:1] == "(" and remove_spaces(ltlf_formula[2:len(ltlf_formula)-2]) in cl.keys():
        return
    if "(" + remove_spaces(ltlf_formula) + ")" in cl.keys():
        return
    if literal:
        split = ltlf_formula.replace(" ", ",").replace("not,", "not ").split()
    else:
        split = ltlf_formula.split()
    if len(split) == 1:                             # positive literal
        cl[ltlf_formula] = LIT
        cl["not " + ltlf_formula] = LIT
        return
    elif len(split) == 2 and split[0] not in [GLOBALLY, EVENTUALLY, NEXT, WEAK_NEXT]:
        if split[0] == NOT:     # negative literal
            cl[ltlf_formula] = LIT
            cl[ltlf_formula.replace("not ", "")] = LIT
            return

    split = ltlf_formula.replace("(", "( ").replace(")", " )").split()
    pointer = ["", sys.maxsize, 0]
    count = 0
    parenthesis = 0
    for elem in split:
        if elem == "(":
            parenthesis += 1
        elif elem == ")":
            parenthesis -= 1
        elif elem in OPERATORS:
            if parenthesis < pointer[1]:
                pointer = [elem, parenthesis, count]
            elif (parenthesis <= pointer[1]) and (has_less_priority(elem, pointer[0])):
                pointer = [elem, parenthesis, count]
        count += 1
    operator = pointer[0]
    if operator == "":
        literal = True
        sigma(ltlf_formula, cl, literal)
        return
    cl[remove_spaces(ltlf_formula)] = operator
    if operator in [AND, OR]:
        subformula = populate_subformula(split, 0, pointer[2])
        sigma(subformula, cl)
        subformula = populate_subformula(split, pointer[2]+1, len(split))
        sigma(subformula, cl)
    elif operator == NEXT or operator == WEAK_NEXT:
        subformula = populate_subformula(split, pointer[2]+2, len(split)-1)
        sigma(subformula, cl)
    elif operator == EVENTUALLY:
        subformula = populate_subformula(split, pointer[2] + 2, len(split)-1)
        sigma(subformula, cl)
        subformula = NEXT + " (" + populate_subformula(split, pointer[2], len(split)) + ")"
        cl[remove_spaces(subformula)] = NEXT
    elif operator == GLOBALLY:
        subformula = populate_subformula(split, pointer[2]+2, len(split)-1)
        sigma(subformula, cl)
        subformula = WEAK_NEXT + " (" + populate_subformula(split, pointer[2], len(split)) + ")"
        cl[remove_spaces(subformula)] = WEAK_NEXT
    elif operator == UNTIL:
        subformula = populate_subformula(split, 1, pointer[2]-1)
        sigma(subformula, cl)
        subformula = populate_subformula(split, pointer[2] + 2, len(split)-1)
        sigma(subformula, cl)
        subformula = NEXT + " (" + populate_subformula(split, 0, len(split)) + ")"
        cl[remove_spaces(subformula)] = NEXT
    elif operator == RELEASE:
        subformula = populate_subformula(split, 1, pointer[2]-1)
        sigma(subformula, cl)
        subformula = populate_subformula(split, pointer[2] + 2, len(split)-1)
        sigma(subformula, cl)
        subformula = WEAK_NEXT + " (" + populate_subformula(split, 0, len(split)) + ")"
        cl[remove_spaces(subformula)] = WEAK_NEXT


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


def extract_general_formulas(dnf):
    new_clauses = dnf.copy()
    for clause in dnf:
        for clause_to_compare in dnf:
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


def simplify_dnf(dnf, alp):
    complete_dnf = complete_clauses(dnf, alp)
    dnf = simplify_equivalent_clauses(complete_dnf)
    compact_fluents = extract_general_formulas(dnf)
    return compact_fluents


def simplify_equivalent_clauses(dnf):
    done = False
    compact_dnf = dnf.copy()
    counter = 0
    while not done:
        set_to_zero = False
        if counter >= len(dnf):
            counter = 0
        dnf_list = list(dnf)
        elem = dnf_list[counter]
        for i in range(counter + 1, len(dnf)):
            elem_to_compare = dnf_list[i]
            if elem != elem_to_compare and len(elem) == len(elem_to_compare):
                del_index = try_literal_deletion(elem, elem_to_compare)
                if del_index != -1:
                    compact_dnf.discard(elem)
                    compact_dnf.discard(elem_to_compare)
                    new_tuple = ()
                    for j in range(0, len(elem)):
                        if j != del_index:
                            new_tuple += (elem[j],)
                    compact_dnf.add(new_tuple)
                    set_to_zero = True
                    break
        if set_to_zero:
            counter = 0
        else:
            counter += 1
        if counter >= len(dnf) and dnf.difference(compact_dnf) == set([]):
            done = True
        else:
            dnf = compact_dnf.copy()
    return compact_dnf


# put the not for the false fluents
def complete_clauses(dnf, alphabet):
    new_dnf = set([])
    for t in dnf:
        new_tuple = []
        alp_index = 0
        tuple_index = 0
        while alp_index < len(alphabet) and tuple_index < len(t):
            elem = t[tuple_index]
            if elem == alphabet[alp_index]:
                new_tuple.append(elem)
                alp_index += 1
                tuple_index += 1
            else:
                new_tuple.append("not " + alphabet[alp_index])
                alp_index += 1
            print(str(new_tuple))
        if tuple_index == len(t):
            for fluent in alphabet[alp_index:]:
                new_tuple.append("not " + fluent)
        tup = ()
        for elem in new_tuple:
            tup += (elem,)
        new_dnf.add(tup)
    return new_dnf


def try_literal_deletion(elem1, elem2):
    num_lit_and_neg = 0
    del_index = -1
    for i in range(0, len(elem1)):
        if elem1[i] != elem2[i]:
            split1 = elem1[i].split("not ")
            split2 = elem2[i].split("not ")
            if len(split1) == 2 and len(split2) == 1:
                if split1[1] == elem2[i]:
                    if num_lit_and_neg == 0:
                        num_lit_and_neg = 1
                        del_index = i
                    else:
                        return -1
            elif len(split1) == 1 and len(split2) == 2:
                if elem1[i] == split2[1]:
                    if num_lit_and_neg == 0:
                        num_lit_and_neg = 1
                        del_index = i
                    else:
                        return -1
            else:
                return -1
    if num_lit_and_neg == 1:
        return del_index
    return -1


def compact_fluents_notation(t_function, s, alp, proposition_combination):
    compact_t_function = {}
    same_state_dict = {}
    for state in s:
        if state not in [TRUE, ENDED, FALSE]:
            for pointer1 in range(0, len(proposition_combination)):
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
        print("NOT COMPACT FLUENT NOTATION: " + str(same_state_dict[key]))
        compact_fluents = simplify_dnf(same_state_dict[key], alp)
        compact_t_function[(state, compact_fluents)] = next_state
    return compact_t_function

def has_less_priority(op1, op2):
    if op1 == AND and op2 == OR:
        return False
    elif op1 == OR and op2 == AND:
        return True
    elif op1 == NEXT or op1 == WEAK_NEXT or op1 == EVENTUALLY or op1 == UNTIL or op1 == RELEASE or op1 == GLOBALLY:
        return False
    elif op2 == NEXT or op2 == WEAK_NEXT or op2 == EVENTUALLY or op2 == UNTIL or op2 == RELEASE or op2 == GLOBALLY:
        return True
    elif op2 == "":
        return True
    else:
        return False


def aux(sub_elem, sub_elem2, rs):
    entry = set([])
    print("Aux sub_elem: " + sub_elem)
    if AND_STATE_SEPARATOR in sub_elem:
        for s_e in sub_elem.split(AND_STATE_SEPARATOR):
            print("Subelem in the and: " + s_e)
            if s_e != sub_elem2 and s_e + AND_STATE_SEPARATOR not in sub_elem2 and \
                                    AND_STATE_SEPARATOR + s_e not in sub_elem2:
                entry.add(s_e)
    else:
        if sub_elem != sub_elem2 and sub_elem + AND_STATE_SEPARATOR not in sub_elem2 and \
                                AND_STATE_SEPARATOR + sub_elem not in sub_elem2:
            entry.add(sub_elem)
    if AND_STATE_SEPARATOR in sub_elem2:
        for e in sub_elem2.split(AND_STATE_SEPARATOR):
            entry.add(e)
    else:
        entry.add(sub_elem2)
    rs.add(frozenset(entry))


def compute_tf_and(input_set):
    if len(input_set) == 1:
        result = ""
        for elem in input_set:
            if len(result) < 1:
                result = elem
            else:
                result += OR_STATE_SEPARATOR + elem
        return result
    rs = set([])
    i = 0
    while i < len(input_set)-1:
        if i == 0:
            elem = input_set[i]
        else:
            elem = ""
            for fs in rs:
                fs_entry = ""
                for f in fs:
                    if len(fs_entry) < 1:
                        fs_entry = f
                    else:
                        fs_entry += AND_STATE_SEPARATOR + f
                if len(elem) < 1:
                    elem = fs_entry
                else:
                    elem += OR_STATE_SEPARATOR + fs_entry
            rs.clear()
        elem2 = input_set[i + 1]
        if OR_STATE_SEPARATOR in elem:
            for sub_elem in elem.split(OR_STATE_SEPARATOR):
                if OR_STATE_SEPARATOR in elem2:
                    for sub_elem2 in elem2.split(OR_STATE_SEPARATOR):
                        aux(sub_elem, sub_elem2, rs)
                else:
                    aux(sub_elem, elem2, rs)
        else:
            if OR_STATE_SEPARATOR in elem2:
                for sub_elem2 in elem2.split(OR_STATE_SEPARATOR):
                    aux(elem, sub_elem2, rs)
            else:
                aux(elem, elem2, rs)
        i += 1
    result = ""
    for fs in rs:
        # The result has to be sorted in order to avoid key error raised by inverted order of the states,
        # e.g. F (a) - G (a) == G (a) - F (a), but in the dictionary the first one is stored. Sorting we
        # avoid this possible scenario
        sorted_list = sorted(fs)
        f_entry = ""
        for s in sorted_list:
            if len(f_entry) < 1:
                f_entry = s
            else:
                f_entry += AND_STATE_SEPARATOR + s
        if len(result) < 1:
            result = f_entry
        else:
            result += OR_STATE_SEPARATOR + f_entry
    return result


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


def sort_and_state(elem):
    and_state_list = sorted(elem.split(AND_STATE_SEPARATOR))
    and_state = ""
    for sub_elem in and_state_list:
        if len(and_state) < 1:
            and_state = sub_elem
        else:
            and_state += AND_STATE_SEPARATOR + sub_elem
    return and_state