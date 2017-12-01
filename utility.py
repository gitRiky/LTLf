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
WEAK_UNTIL = "R"
GLOBALLY = "G"
EVENTUALLY = "F"

AND_STATE_SEPARATOR = " - "
OR_STATE_SEPARATOR = ", "

OPERATORS = [AND, OR, NEXT, WEAK_NEXT, UNTIL, GLOBALLY, EVENTUALLY, WEAK_UNTIL]


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
    if formula_type == UNTIL or formula_type == WEAK_UNTIL:
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
    elif operator == WEAK_UNTIL:
        subformula = populate_subformula(split, 1, pointer[2]-1)
        sigma(subformula, cl)
        subformula = populate_subformula(split, pointer[2] + 2, len(split)-1)
        sigma(subformula, cl)
        subformula = WEAK_NEXT + " (" + populate_subformula(split, 0, len(split)) + ")"
        cl[remove_spaces(subformula)] = WEAK_NEXT


def has_less_priority(op1, op2):
    if op1 == AND and op2 == OR:
        return False
    elif op1 == OR and op2 == AND:
        return True
    elif op1 == NEXT or op1 == WEAK_NEXT or op1 == EVENTUALLY or op1 == UNTIL or op1 == WEAK_UNTIL or op1 == GLOBALLY:
        return False
    elif op2 == NEXT or op2 == WEAK_NEXT or op2 == EVENTUALLY or op2 == UNTIL or op2 == WEAK_UNTIL or op2 == GLOBALLY:
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
    print(str(input_set))
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