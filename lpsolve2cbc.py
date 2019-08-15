import re
from arpeggio import Optional, ZeroOrMore, OneOrMore, EOF, OrderedChoice, NoMatch
from arpeggio import RegExMatch as _
from arpeggio import ParserPython, PTNodeVisitor, visit_parse_tree
import json
from pprint import pprint,pformat
import argparse
from ortools.linear_solver import pywraplp


def scinot():     return _(r'\d+\.\d+e\+\d+|\d+e\+\d+')
def number():     return _(r'\d*\.\d+|\d+')
def gennum():     return OrderedChoice([scinot,number])
def factor():     return Optional(["+","-"]), [gennum, ("(", expression, ")")]
def term():       return Optional(["+", "-"]), OrderedChoice([(ZeroOrMore([gennum]), Optional(['*']), varname), gennum])
def varname():    return _(r'[a-zA-Z_][a-zA-Z0-9_]*')
def expr():       return term, ZeroOrMore(OneOrMore(["+", "-"], term))
def obj():        return _(r'min|max'), ':', expr, ';'
def compare():    return OrderedChoice(['>=','<=','<','=','>'])
def constr():     return varname, ':', expr, compare, expr, Optional(compare, expr),';'
def vardef():     return _(r'bin|int'), varname, ZeroOrMore(',', varname), ';'
def prog():       return obj, ZeroOrMore(constr)
#def calc():       return OneOrMore(expression), EOF

def tt():         return varname, ':', varname, compare, gennum, ';'

constr_par = ParserPython(constr).parse
obj_par = ParserPython(obj).parse
tt_par = ParserPython(constr).parse
vardef_par = ParserPython(vardef).parse


def addcoeff(obj,term,mult=1):
    if term[1] not in obj:
        obj[term[1]] = 0

    obj[term[1]] += term[0] * mult
    return obj


class ConstraintVisitor(PTNodeVisitor):
    def visit_varname(self, node, children):
        """
        Just returns list of child nodes (bibentries).
        """
        # Return only dict nodes
        return {'type':'var','val':str(node)}
        
    def visit_number(self, node, children):
        return {'type':'num','val':float(node.value)}

    def visit_scinot(self, node, children):
        return {'type':'num','val':float(node.value)}

    def visit_term(self, node, children):
        if self.debug:
            print("TERM",node)
        mult = 1
        o = {}
        for child in children:
            if self.debug:
                print('CHILD',child) 
            if child == '-':
                mult = -1
            else:
                if 'type' in child:
                    if child['type'] == 'num':
                        if self.debug:
                            print('COEFF MULT',child['val'], mult,child['val'] * mult)
                        o['coeff'] = child['val'] * mult
                    elif child['type'] == 'var':
                        if self.debug:
                            print('COEFF VAR',child['val'])
                        o['var'] = child['val']
                    else:
                        print('UNRECOGNIZED TYPE',child['type'])
                        exit(1)
        if 'coeff' not in o:
            o['coeff'] = 1
        if 'var' not in o:
            o['var'] = 'CONSTANT'
        if self.debug:
            print('O',o) 
        return [(o['coeff'],o['var'])]

    def visit_expr(self, node, children):
        vals = []
        for child in children:
            vals.append(child)
        return vals

    def visit_constr(self, node, children):
        o = {}
        o['name'] = children[0]['val']
        oconstr = {}
        mult = 1
        for ch in children[1]:
            if self.debug:
                print('CH',ch) 
            if ( ch == '+' ):
                mult = 1
            elif ( ch == '-' ):
                mult = -1
            else:
                for lchild in ch:
                    if self.debug:
                        print('LCHILD',lchild) 
                    oconstr = addcoeff(oconstr,lchild,mult)
        o['compare'] = children[2]
        mult = 1
        for ch in children[3]:
            if self.debug:
                print('CH',ch) 
            if ( ch == '+' ):
                mult = 1
            elif ( ch == '-' ):
                mult = -1
            else:
                for rchild in ch:
                    if self.debug:
                        print('rchild',rchild) 
                    oconstr = addcoeff(oconstr, rchild, -1*mult) # move to left side

        o['left'] = oconstr
        o['right'] = {'CONSTANT': 0}
        if self.debug:
            print('CO',o) 
        return o

    def visit_obj(self, node, children):
        o = {}
        if self.debug:
            print('OBJCHILD',children) 
        o['obj'] = children[0]
        oobj = {}
        
        mult = 1
        for ch in children[1]:
            if self.debug:
                print('CH',ch) 
            if ( ch == '+' ):
                mult = 1
            elif ( ch == '-' ):
                mult = -1
            else:
                for ochild in ch:
                    if self.debug:
                        print('ochild',ochild) 
                    oobj = addcoeff(oobj, ochild, mult)
        o['left'] = oobj
        if self.debug:
            print('OO',o) 
        return o
        
    def visit_vardef(self, node, children):
        o = {}
        o['type'] = str(children[0])
        o['vars'] = []
        for ci in range(1,len(children)):
            next = children[ci]
            if next == ',':
                pass
            else:
                if self.debug:
                    print('next',next)
                o['vars'].append(next['val'])
        return o

def main():

    parser = argparse.ArgumentParser(description='Solve assignment of passenger trips to vehicles, given time windows and resource constraints')
    parser.add_argument('--lpfile', type=str, dest='lpfile',
                        default='/dev/stdin',
                        help='File to read lp from')
    parser.add_argument('--echo', dest='echo',action='store_true',
                        help='echo MILP to screen')
    parser.add_argument('--debug', dest='debug',action='store_true',
                        help='show debug info')
    parser.add_argument('--relax-integer', dest='relaxInteger',action='store_true',
                        help='Remove integer constraints to aid debugging')
    parser.add_argument('--precision', dest='precision',type=float,
                        help="Precision with which to test the result")
    parser.set_defaults(echo=False)
    parser.set_defaults(debug=False)
    parser.set_defaults(relaxInteger=False)
    parser.set_defaults(precision=1e-7)
    args = parser.parse_args()


    with open(args.lpfile) as f:
        content = f.readlines()

    # you may also want to remove whitespace characters like `\n` at the end of each line
    content = [x.strip() for x in content]
    content = "".join([re.sub("#.*$","",x) for x in content])
    #print(content.split(";"))


    objp = None
    vardefs = []
    constr = []
    constrdone = False

    debug = args.debug
    prog = {'constr':[]}
    for line in content.split(";"):
        done=False
        if not re.match(r'^\s*$',line):
            l = line + " ;"
            if debug:
                print('L',l)
            while not done:
                if objp == None:
                    objp = ParserPython(obj).parse(l)
                    prog['obj']=visit_parse_tree(objp, ConstraintVisitor(debug=debug))
                    if debug:
                        print('OBJ',prog['obj'])
                    done = True
                elif not constrdone:
                    try:
                        cc=constr_par(l)
                        vpt = visit_parse_tree(cc, ConstraintVisitor(debug=debug))
                        prog['constr'].append(vpt)
                        if debug:
                            print('CC',vpt)
                        done = True
                    except NoMatch:
                        constrdone = True
                else:
                    vd=ParserPython(vardef).parse(l)
                    vdt = visit_parse_tree(vd, ConstraintVisitor(debug=debug))
                    vardefs.append(vdt)
                    if debug:
                        print('VD',vdt)
                    done = True

    allvar={}
    for var, coeff in prog['obj']['left'].items():
        if var != 'CONSTANT':
            allvar[var] = 'gtzero'
    for constr in prog['constr']:
        for var, coeff in constr['left'].items():
            if var != 'CONSTANT':
                allvar[var] = 'gtzero,'
    for vd in vardefs:
        for var in vd['vars']:
            if var != 'CONSTANT':
                if vd['type'] == 'bin':
                    allvar[var] = allvar[var]+'bin'
                elif vd['type'] == 'int':
                    allvar[var] = allvar[var]+'int'
                elif vd['type'] == 'free':
                    allvar[var] = 'free,'+allvar[var].replace("gtzero","")
                else:
                    raise Exception("UNKNOWN VARTYPE "+vd['type'])

    allconstr={}

    #print(allvar)
    solver = pywraplp.Solver('SolveIntegerProblem',
                             pywraplp.Solver.CBC_MIXED_INTEGER_PROGRAMMING)
    for varname,vartype in allvar.items():
        if varname != 'CONSTANT':
            if re.match('.*int.*',vartype):
                low = 0
                hi  = solver.infinity()
                if re.match(r'.*free.*',vartype): low = -solver.infinity()
                if args.relaxInteger:
                    allvar[varname] = solver.NumVar(low, hi, varname)
                else:
                    allvar[varname] = solver.IntVar(low, hi, varname)
                # print ("[%s] INTVAR %s: %f, %f" % (vartype, varname, low, solver.infinity()))

            elif re.match(r'.*bin.*',vartype) and re.match(r'.*free.*',vartype):
                raise Exception("Can't declare variable "+vartype+" as both free and bin")

            elif re.match(r'.*bin.*',vartype):
                if args.relaxInteger:
                    allvar[varname] = solver.NumVar(0.0, 1.0, varname)
                else:
                    allvar[varname] = solver.IntVar(0.0, 1.0, varname)
                # print ("[%s] BINVAR %s: %f, %f" % (vartype, varname, 0, 1))

            else:
                low = 0
                hi  = solver.infinity()
                if re.match(r'free',vartype): low = -solver.infinity()
                allvar[varname] = solver.NumVar(0,solver.infinity(),varname)
                # print ("[%s] NUMVAR %s: %f, %f" % (vartype, varname, low, hi))
    
    def coeff_fn(vardict,name,default=0):
        if name in vardict:
            return vardict[name]
        else:
            return default


    varstat = {}
    objective = solver.Objective()
    dumps = ""
    for varname, coeff in prog['obj']['left'].items():
        if varname != 'CONSTANT':
            objective.SetCoefficient(allvar[varname],coeff)
            if coeff != 0 and varname not in varstat.keys():
                varstat[varname] = { 'obj': True, 'constr': [] }
            dumps += " + (%f) %s" % (coeff,varname)

    if prog['obj']['obj'] == 'min':
        objective.SetMinimization()
    elif prog['obj']['obj'] == 'max':
        objective.SetMaximization()
    else:
        raise Exception("Unknown objective "+prog['obj']['obj'])
    if args.echo:
        print(prog['obj']['obj'],dumps)

    for constr in prog['constr']:
        #print('CC',constr)
        if constr['compare'] == '<=' or constr['compare'] == '<':
            low  = -solver.infinity()
            hi   = -coeff_fn(constr['left'],'CONSTANT') + coeff_fn(constr['right'],'CONSTANT')
            bound = hi
        elif constr['compare'] == '>='  or constr['compare'] == '>':
            low   = -coeff_fn(constr['left'],'CONSTANT')  + coeff_fn(constr['right'],'CONSTANT')
            hi   = solver.infinity()
            bound = low
        elif constr['compare'] == '=':
            low  = -coeff_fn(constr['left'],'CONSTANT')  + coeff_fn(constr['right'],'CONSTANT')
            hi   = low
            bound = low
        else:
            raise Exception("UNHANDLED COMPARISON OPERATOR "+constr['compare'])

        allconstr[constr['name']] = solver.Constraint(low,hi)
        dumps = ""
        for varname, coeff in constr['left'].items():
            if ( varname != "CONSTANT" ):
                allconstr[constr['name']].SetCoefficient(allvar[varname],coeff)
                dumps += " + (%f) %s" % (coeff,varname)
                if varname not in varstat.keys():
                    varstat[varname] = { 'obj': False, 'constr': [] }
                varstat[varname]['constr'].append(constr['name'])
                
        if args.echo:
            print ("%s: %s %s %f;" % (constr['name'],dumps,constr['compare'],bound))


    # check if all vars in objective exist in contraints
    for varname,vs in varstat.items():
        if vs['obj'] and len(vs['constr']) == 0:
            raise Exception("Variable "+varname+" in objective but not in any constraints "+pformat(vs))


    result_status = solver.Solve()

    resdict = {
        0: 'optimal',
        1: 'feasible',
        2: 'infeasible',
        3: 'unbounded',
        4: 'abnormal',
        5: 'model_invalid',
        6: 'not_solved'
    }
    if ( result_status != pywraplp.Solver.OPTIMAL ):
         print('RESULT STATUS', repr(result_status),'=',resdict[result_status])

    # The problem has an optimal solution.
    assert result_status == pywraplp.Solver.OPTIMAL

    # The solution looks legit (when using solvers other than
    # GLOP_LINEAR_PROGRAMMING, verifying the solution is highly recommended!).
    assert solver.VerifySolution(args.precision, True)

#    print('Number of variables =', solver.NumVariables())
#    print('Number of constraints =', solver.NumConstraints())

    # The objective value of the solution.
    print('Value of objective function: %f' % solver.Objective().Value())
    print()
    # The value of each variable in the solution.

    print('Actual value of the variables:')
    for varname,variable in allvar.items():
        print('%-40s  %f' % (variable.name(), variable.solution_value()))

if __name__ == '__main__':
  main()
