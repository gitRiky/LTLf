import sys
import codecs

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

automaton_states = {}
NEXT_STATE_FILE_PATH = "/home/riccardo/fs/workspace/nextState.txt"
CL_FILE_PATH = "/home/riccardo/fs/workspace/cl.txt"


def remove_spaces(form):
    form = form.replace("( ", "(").replace(" )", ")")
    return form


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


# I can add an optimization: Let's start building the left subformula using two variables:
# temp_subf and subf. When we change the pointer, we update the temp_subf while the subf will be updated always
# if the pointer changes again, then temp_subf = subf and we continue
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


def main():
    goal = sys.argv[1]
    cl = {}
    sigma(goal, cl)
    with codecs.open(NEXT_STATE_FILE_PATH, "w") as file_handle:
        goal = goal.replace(" ", "*")
        file_handle.write(goal)
    with codecs.open(CL_FILE_PATH, "w") as file_handle:
        for key in cl.keys():
            pair = key + "\t" + cl[key] + "\n"
            file_handle.write(pair)

main()
