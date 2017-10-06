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


TEST_FILE = "test.txt"


Q = []
automaton_states = {}


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
    if par != 0:
        print("Formula to be adjusted: " + ltlf_formula)
    if par > 0:
        ltlf_formula = ltlf_formula[par*2:]
    elif par < 0:
        ltlf_formula = ltlf_formula[:par*2]
    if par != 0:
        print("Adjusted formula: " + ltlf_formula)
    return ltlf_formula


def sigma(ltlf_formula, cl, literal=False):
    print("FORMULA: " + ltlf_formula)
    if remove_spaces(ltlf_formula) in cl.keys():                         # formula already in CL
        print("Sub-formula " + str(ltlf_formula) + " already in Q")
        return
    elif ltlf_formula[:1] == "(" and remove_spaces(ltlf_formula[2:len(ltlf_formula)-2]) in cl.keys():
        print("Sub-formula " + str(ltlf_formula) + " already in Q")
        return
    elif "(" + remove_spaces(ltlf_formula) + ")" in cl.keys():
        print("Sub-formula " + str(ltlf_formula) + " already in Q")
        return
    if literal:
        split = ltlf_formula.replace(" ", ",").replace("not,", "not ").split()
    else:
        split = ltlf_formula.split()
    print(split)
    if len(split) == 1:                             # positive literal
        print("I'm adding a positive literal " + ltlf_formula)
        cl[ltlf_formula] = LIT
        cl["not " + ltlf_formula] = LIT
        return
    elif len(split) == 2 and split[0] not in [GLOBALLY, EVENTUALLY, NEXT, WEAK_NEXT]:
        if split[0] == NOT:     # negative literal
            print("I'm adding a negative literal " + ltlf_formula)
            cl[ltlf_formula] = LIT
            cl[ltlf_formula.replace("not ", "")] = LIT
            return

    split = ltlf_formula.replace("(", "( ").replace(")", " )").split()
    print(split)
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
                print("Pointer: ", pointer)
            elif (parenthesis <= pointer[1]) and (has_less_priority(elem, pointer[0])):
                pointer = [elem, parenthesis, count]
                print("Pointer: ", pointer)
        count += 1
    operator = pointer[0]
    print("Operator: " + operator)
    if operator == "":
        literal = True
        print("Literal = True")
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
        print("UNTIL: ", subformula)
        cl[remove_spaces(subformula)] = NEXT
    elif operator == WEAK_UNTIL:
        subformula = populate_subformula(split, 1, pointer[2]-1)
        sigma(subformula, cl)
        subformula = populate_subformula(split, pointer[2] + 2, len(split)-1)
        sigma(subformula, cl)
        subformula = WEAK_NEXT + " (" + populate_subformula(split, 0, len(split)) + ")"
        cl[remove_spaces(subformula)] = WEAK_NEXT


def obtain_automaton_states(goal):
    cl = {}
    sigma(goal, cl)
    counter = 0
    q = []
    for key in cl.keys():
        if key != goal:
            counter += 1
            automaton_states["q" + str(counter)] = [key, cl[key]]
        else:
            automaton_states["q0"] = [key, cl[key]]
    for state in automaton_states.keys():
        print("State " + state + ", Formula: " + automaton_states[state][0] +
              ", Type: " + automaton_states[state][1])
        q.append(state)
    return automaton_states
