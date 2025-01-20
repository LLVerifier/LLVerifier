#!/bin/python3
from lark import Lark, Transformer ,Tree, Token, Visitor
import copy
import pdb

IStateMAP = {}#key:prinname,value:attributes

def fixpoint(last,f):
    #f should not modify i
    while True:
        new = f(last)
        if new == last:
            break
        else:
            last = new
    return new

def addDefaultAttributes():
    #deporecated now
    for k,v in IStateMAP.items():
        if k in ['userA','userC']:
            #modify v
            v.add(PAIR(QID('know'),SET(QID('secret'+k[-1]))))

def removeUselessFromAttributes():
    def helper(s:'SET|Item'):
        if isinstance(s,DOTS):
            s = SET()
        elif isinstance(s,SET):
            s.remove(DOTS())
            s.remove(NILS())
            helper(s.v)
        elif isinstance(s,PAIR):
            helper(s.v)
        elif isinstance(s,tuple):
            for i in s:
                helper(i)
    for k,v in IStateMAP.items():
        helper(v)

def typeAnnotate4IstateMAP():
    def changeVal(ptr,v,idx=0):
        if isinstance(ptr,str):
            IStateMAP[ptr] = v2type(v)
        elif isinstance(ptr,SET):
            ptr.update(idx,v2type(v))
        else:
            print('wrong!')
    for k,v in IStateMAP.items():
        modifyLeaves(k,v,0,changeVal)

def genInitTemplate():
    #typeAnnotate4IstateMAP()
    removeUselessFromAttributes()
    #addDefaultAttributes()
    l = []
    for k,v in IStateMAP.items():
        l.append(INTERNAL_STATE(k,v))
    return ' '.join([str(istate) for istate in l])

def normalize(att):
    #return att
    '''
SET[SET[A],B,...] => SET[A,B]
    '''
#one item the same, handle inside, two more items, check the first, up one level
#SET(DeviceB : SET(SET(SET(SET(A,), B), C), D),)
#SET(SET(SET(SET(A,), B), C), D)
#SET(SET(SET(A,), B), C, D)
#SET(SET(A,), B, C, D)
#SET(A, B, C, D)
    def helper(l):
        #pdb.set_trace()
        if isinstance(l,PAIR):
            return PAIR(l.k,helper(l.v))
        elif isinstance(l,SET):
            if len(l.v) > 1:# two more items
                #pdb.set_trace()
                if isinstance(l.v[0],SET):
                    return SET(*l.v[0].v,*l.v[1:])
                else:
                    return SET(helper(l.v[0]),*l.v[1:])
            else:#one item
                return SET(helper(l.v[0]))
        return l
    return fixpoint(att,helper)

class ASTVisitor(Visitor):
    def visitInternalState(self,i):
        print(i)

    def __default__(self, tree):
        for child in tree.children:
            if isinstance(child, Tree):
                pass
            elif isinstance(child, Token):
                pass
            elif isinstance(child, EQUATIONAL_RULE):
                for i in child.lhs:
                    self.visitInternalState(i)
                for i in child.rhs:
                    self.visitInternalState(i)


populateIStateMap = lambda varmap,tree: attributesCombiner(varmap).visit(tree)
annotateTypes = lambda tree: typesAnnotator().visit(tree)

def v2type(s):
    downcase = lambda i : i[0]+i[1:].lower()
    if isinstance(s,VARIABLE):
        return TYPE([s.type_])
    elif isinstance(s,QID) or isinstance(s,int):
        return s
    else:
        return TYPE([downcase(s.__class__.__name__)])

def modifyLeaves(ptr,s,i,f):
    '''
    Modify leaf element using pointer ptr and callback function f, replacing s to i
    '''
    if isinstance(s,INTERNAL_STATE):
        modifyLeaves(s,s.attributes,i,f)
    elif isinstance(s,SET):
        modifyLeaves(s,s.v,i,f)
    elif isinstance(s,PAIR):
        modifyLeaves(s,s.k,i,f)
        modifyLeaves(s,s.v,i,f)
    elif isinstance(s,tuple):
        for idx,item in enumerate(s):
            modifyLeaves(ptr,item,idx,f)
    elif isinstance(s,DOTS) or isinstance(s,NILS):
        return
    elif isinstance(s,VARIABLE):
        f(ptr,s,i)
    else: #QID,BOOL,etc
        f(ptr,s,i)

class typesAnnotator(ASTVisitor):
    def visitInternalState(self,i):
        def changeVal(ptr,v,idx=0):
            if isinstance(ptr,str):
                IStateMAP[ptr] = v2type(v)
            elif isinstance(ptr,SET):
                ptr.update(idx,v2type(v))
            elif isinstance(ptr,PAIR):
                ptr.k = v2type(v)
            elif isinstance(ptr,typesAnnotator):
                pass
            else:
                print('wrong!',ptr)

        modifyLeaves(self,i,0,changeVal) 

def combineAttributes(a1:'SET',a2:'SET'):
    a3 = copy.deepcopy(a2)
    for att in a1.v:
        if isinstance(att, PAIR):
            if att.k in a3.keys():
                att3 = a3.get(att.k)
                a3v = a3.vals(att.k)
                att3.v = combineAttributes(att3.v,att.v)
            else:
                a3.add(att)
        #elif isinstance(att,DOTS):
        elif isinstance(att,DOTS) or isinstance(att,NILS):
            #print('in1')
            pass
        else:#item
            if att not in a3.v:
                #print('in2',att,a3.v)
                a3.add(att)
    return a3


class attributesCombiner(ASTVisitor):
    def __init__(self,varmap):
        self.varmap = varmap
        super().__init__()
    def visitInternalState(self,i):
        if isinstance(i,INTERNAL_STATE):
            principal = i.principal
            attributes = i.attributes
            if isinstance(principal,VARIABLE):
                #lookup type
                if self.varmap[principal.ident] == 'User':
                    prinnames = ['userA','userC']
                else: #self.varmap[principal.ident] in ['Device','Server','App','Cloud']:
                    downcase = lambda a : a[0].lower()+a[1:]
                    #downcase = lambda a : a.lower()
                    prinnames = [downcase(self.varmap[principal.ident])+'B']
            else:
                prinnames = [principal.ident]
            for prinname in prinnames:
                #print('handle',i,prinname)
                if prinname in IStateMAP:
                    IStateMAP[prinname] = combineAttributes(IStateMAP[prinname],attributes)
                else:
                    IStateMAP[prinname] = attributes

# Define the grammar for Les
iot_logic_grammar = """
    start: equational_rule+

    equational_rule: "eq" logical_state "=" logical_state " ." | "ceq" logical_state "=" logical_state "if" condition " ."

    condition: arith CMP arith

    arith: number OP number | "(" arith ")" | number

    number: VARIABLE | INTEGER
    
    OP: "+" | "-" | "*" | "/"
    CMP: ">" | "<" | ">=" | "<=" | "==" | "=/="

    logical_state: (internal_state | event)*

    internal_state: "<" principal "|" attributes ">" 

    event: "$" principal action principal "|" arguments
         | "$" principal action principal

    principal.1: USER | DEVICE | CLOUD | APP | SERVER | CLIENT | VARIABLE

    USER: "user" STRING
    DEVICE: "device" STRING
    CLOUD: "cloud" STRING
    APP: "app" STRING
    SERVER: "server" STRING
    CLIENT: "client" STRING

    pair: qid ":" set | principal ":" set

    item: BOOL | qid | INTEGER | principal | pair | DOTS | VARIABLE

    list: list ";" item | item

    set: NILS | "(" set "," item ")" | set "," item | item | "(" item ")"

    arguments: "(" list ")" | list 

    attributes: set 

    action: qid

    qid.2: "'" STRING "'" 

    BOOL: "true" | "false"
    NILS: "nils"
    DOTS: "..."/\\./* 
    VARIABLE: /[A-Z]//[a-zA-Z0-9_]/* 

    STRING: /[a-zA-Z0-9_:]+/
    INTEGER: /[0-9]+/

    %import common.WS
    %ignore WS
"""
class AST:
    def __str__(self):
        return self.__repr__()
    def __hash__(self):
        return hash(tuple(self.__dict__))
    def __eq__(self,other):
        if self.__class__ == other.__class__:
            if self.__dict__ == other.__dict__:
                return True
        return False
class EQUATIONAL_RULE(AST):
    def __init__(self,lhs,rhs,condition=None):
        super().__init__()
        self.lhs = lhs
        self.rhs = rhs
        self.condition = condition
    def __repr__(self):
        if self.condition:
            return f'ceq {self.lhs} = {self.rhs} if {self.condition}'
        else:
            return f'eq {self.lhs} = {self.rhs}'

class INTERNAL_STATE(AST):
    def __init__(self,p,a):
        super().__init__()
        self.principal = p
        self.attributes = a
    def __repr__(self):
        return f'< {self.principal} | {self.attributes} >'

class EVENT(AST):
    def __init__(self,i0,i1,i2,i3=None):
        super().__init__()
        self.subject = i0
        self.action = i1
        self.object = i2
        self.arguments = i3
    def __repr__(self):
        if self.arguments:
            return f'$ {self.subject} {self.action} {self.object} | {self.arguments}'
        else:
            return f'$ {self.subject} {self.action} {self.object}'
    def __eq__(self,other):
        if self.__class__ == other.__class__:
            return variableNormalize(self) == variableNormalize(other)
        return False

class PRINCIPAL(AST):
    def __init__(self,type_,i):
        super().__init__()
        self.type_ = type_
        self.ident = i
    def __repr__(self):
        return self.ident
class DOTS(AST): 
    def __repr__(self):
        return '...'
class NILS(AST):
    def __repr__(self):
        return 'nils'
class VARIABLE(AST):
    def __init__(self,i,type_):
        super().__init__()
        self.ident = i
        self.type_ = type_
    def __repr__(self):
        return self.ident
class QID(AST):
    def __init__(self,i):
        super().__init__()
        self.ident = i
    def __repr__(self):
        return "'"+self.ident+"'"
class PAIR(AST):
    def __init__(self,k,v):
        super().__init__()
        self.k = k
        self.v = v
    def __repr__(self):
        return f'{self.k} : {self.v}'
class SET(AST):
    def __init__(self,*tup):
        super().__init__()
        self.v = tup
    def binary(self):
        return isinstance(self.v,tuple) and len(self.v) == 2
    def add(self,item):
        if len(self.v) == 0:
            self.v = (item)
        else:
            self.v = (*self.v,item)
    def remove(self,item):
        v2 = ()
        for i in self.v:
            if i != item:
                v2 = (*v2,i)
        self.v = v2
    def keys(self):
        return [i.k for i in self.v if isinstance(i,PAIR)]
    def update(self,idx,v):
        l = list(self.v)
        l[idx] = v
        self.v = tuple(l)
        return self.v
    def get(self,k):
        for i in self.v:
            if isinstance(i,PAIR) and i.k == k:
                return i
    def vals(self,k):
        for i in self.v:
            if isinstance(i,PAIR) and i.k == k:
                return i.v
    def __repr__(self):
        return f'SET{self.v}'
    def __str__(self):
        if len(self.v)>1:
            return '('+' , '.join([str(i) for i in self.v])+')'
        elif len(self.v) == 1:
            return str(self.v[0])
        else:
            return 'empty'
    def __copy__(self):
        return SET(*self.v)
class LIST(AST):
    def __init__(self,v):
        super().__init__()
        self.v = v
    def binary(self):
        return len(self.v) == 2
    def __repr__(self):
        return f'LIST{self.v}'
    def __str__(self):
        return '('+' ; '.join([str(i) for i in self.v])+')'
class BOOL(AST):
    def __init__(self,v):
        super().__init__()
        self.v = v
    def __repr__(self):
        if self.v:
            return 'true'
        else:
            return 'false'
class TYPE(AST):#meta type, no use in specifications 
    def __init__(self,v):
        self.v = v# a list of class, e.g., [BOOL , PRINCIPAL , QID]
        super().__init__()
    def __str__(self):
        return '['+' | '.join(self.v)+']'

class CONDITION(AST):
    def __init__(self,i):
        super().__init__()
        self.ident = i
    def __repr__(self):
        return self.ident.__repr__()

class ARITH(AST):
    def __init__(self,items):
        super().__init__()
        self.v = items
    def __repr__(self):
        s = ''
        for i in self.v:
            s += i.__repr__()
        return s

def variableNormalize(evt:'AST'):
    # return a string that after normalize vairable names
    nameMap = {}
    typeVarCnt = {}
    replaces = []
    def rename(i):
        if isinstance(i,VARIABLE):
            if i.type_ not in typeVarCnt:
                typeVarCnt[i.type_] = 1
            if i.ident not in nameMap:
                nameMap [i.ident] = i.type_+str(typeVarCnt[i.type_])
                typeVarCnt[i.type_] += 1
            replaces.append((i.ident,nameMap[i.ident]))
        elif isinstance(i, LIST):
            for ii in i.v:
                rename(ii) 
    rename(evt.subject)
    rename(evt.action)
    rename(evt.object)
    rename(evt.arguments)
    rst = str(evt)
    for o,n in replaces:
        rst = rst.replace(o,n)
    return rst

# Define a transformer to convert the parse tree into Python data structures
class LesTransformer(Transformer):
    def __init__(self,varmap):
        self.varmap = varmap
        super().__init__()
    def equational_rule(self, items):
        if len(items) > 2:
            return EQUATIONAL_RULE(items[0], items[1],items[2])
        else:
            return EQUATIONAL_RULE(items[0], items[1])

    def condition(self,items):
        return CONDITION(items)

    def arith(self,items):
        return ARITH(items)

    def logical_state(self, items):
        return items

    def internal_state(self, items):
        return INTERNAL_STATE(items[0], items[1])

    def event(self, items):
        if len(items) == 4:
            return EVENT(items[0], items[1], items[2], items[3])
        else:
            return EVENT(items[0], items[1], items[2])

    def principal(self, items):
        return items[0]

    def USER(self, items):
        return PRINCIPAL("User", str(items))

    def DEVICE(self, items):
        return PRINCIPAL("Device", str(items))

    def CLOUD(self, items):
        return PRINCIPAL("Cloud", str(items))

    def APP(self, items):
        return PRINCIPAL("App", str(items))

    def SERVER(self, items):
        return PRINCIPAL("Server", str(items))

    def CLIENT(self, items):
        return PRINCIPAL("Client", str(items))

    def pair(self, items):
        return PAIR(items[0], items[1])

    def item(self, items):
        return items[0]

    def list(self, items):
        #return ("list", items)
        return LIST(items)

    def set(self, items):
        #if len(items) == 1 and isinstance(items[0],NILS):
        #    return SET()
        #else:
        return SET(*tuple(items))

    def arguments(self, items):
        return items[0]

    def attributes(self, items):
        return normalize(items[0])
        #return items[0]

    def action(self, items):
        return items[0]

    def qid(self, items):
        i = items[0]
        if isinstance(i,VARIABLE):
            return i
        else:
            return QID(i)

    def STRING(self,items):
        return str(items)

    def INTEGER(self,items):
        return int(items)

    def VARIABLE(self,items):
        return VARIABLE(str(items),self.varmap[str(items)])

    def BOOL(self,items):
        if str(items) == 'true':
            return BOOL(True)
        else:
            return BOOL(False)

    def DOTS(self,items):
        return DOTS()
    def NILS(self,items):
        return NILS()
        #return SET()

class LesTransformer2(LesTransformer):
    def attributes(self, items):
        return items[0]

# Example of parsing an Les rule
code1 = '''\
eq < UserA | 'localTo' : DeviceB , ... > < DeviceB | 'pressed' : false , ... > $ UserA 'pressButton' DeviceB
 = < UserA | 'localTo' : DeviceB , ... > < DeviceB | 'pressed' : true , ... > .
eq < DeviceB | 'pressed' : true , 'key' : false , ... > < UserA | 'localTo' : DeviceB , ... > $ UserA 'callAPI:setKey' DeviceB | KeyC
 = < DeviceB | 'pressed' : false , 'key' : KeyC , ... > < UserA | 'localTo' : DeviceB , ... > $ DeviceB 'callAPI:setKey' cloudA | KeyC .
eq < DeviceB | 'pressed' : true , 'key' : KeyD , ... > < UserA | 'localTo' : DeviceB , ... > $ UserA 'callAPI:setKey' DeviceB | KeyC
 = < DeviceB | 'pressed' : false , 'key' : KeyC , ... > < UserA | 'localTo' : DeviceB , ... > $ DeviceB 'callAPI:setKey' cloudA | KeyC .
eq < DeviceB | 'pressed' : true , 'key' : KeyD , ... > < UserA | 'localTo' : DeviceB , ... > $ UserA 'callAPI:getKey' DeviceB
 = < DeviceB | 'pressed' : true , 'key' : KeyD , ... > < UserA | 'localTo' : DeviceB , ... > $ DeviceB 'sendKey' UserA | KeyD .
eq < cloudA | DeviceB : ('bdKey' : KeyE , ...) > $ DeviceB 'callAPI:setKey' cloudA | KeyC
 = < cloudA | DeviceB : ('bdKey' : KeyC , ...) > .
eq < cloudA | DeviceB : ('bdKey' : KeyC , 'owner' : false , ...) > $ UserA 'callAPI:bind' cloudA | (DeviceB ; KeyC)
 = < cloudA | DeviceB : ('bdKey' : KeyC , 'owner' : UserA , ...) > .
eq < cloudA | DeviceB : ('bdKey' : KeyC , 'owner' : UserD , ...) > $ UserA 'callAPI:reset' cloudA | (DeviceB ; KeyC)
 = < cloudA | DeviceB : ('bdKey' : KeyC , 'owner' : false , ...) > .
'''
code2 = '''\
eq < ServerB | 'key' : 'secret' , ... > $ ClientA 'open' DeviceB 
 = < ServerB | 'key' : 'secret' , ... > $ ServerB 'sendKey' ServerC | 'secret' .
ceq < cloudA | DeviceB : ( 'bdKey' : KeyC , 'owner' : false , ... ) , ... > $ UserA 'callAPI:bind' cloudA | ( DeviceB ; KeyD )
 = < cloudA | DeviceB : ( 'bdKey' : KeyC , 'owner' : UserA , ... ) , ... >
if KeyD == KeyC .
'''
def test(code):
    #varmap = {'DeviceB':'Device','UserA':'User','UserC':'User','KeyB':'Qid','KeyC':'Qid'}
    #varmap = {'DeviceB':'Device','UserA':'User','UserD':'User','KeyC':'Qid','KeyD':'Qid','KeyE':'Qid'}
    varmap = {'DeviceB':'Device','DeviceX':'Device','KeyA':'Qid','KeyC':'Qid','KeyD':'Qid','KeyB':'Qid','UserA':'User','UserX':'User'}
    varmap.update({'ServerB':'Server','ServerC':'Server','ClientA':"Client"})
    parser = Lark(iot_logic_grammar, parser='earley')
    #parser = Lark(iot_logic_grammar, parser='lalr')
    tree = parser.parse(code)
    #print(tree.pretty())
    transformer = LesTransformer(varmap)
    #AST_without_normal = LesTransformer2(varmap).transform(tree)
    AST = transformer.transform(tree)
    #print(AST_without_normal)
    #print()
    print(AST)
    print()

    annotateTypes(AST)
    print(AST)
    print()

    populateIStateMap(varmap,AST)
    print(IStateMAP)
    print(genInitTemplate())
    print(IStateMAP)
    return AST

def parseAST(code,varmap):
    parser = Lark(iot_logic_grammar, parser='earley')
    transformer = LesTransformer(varmap)
    tree = parser.parse(code)
    AST = transformer.transform(tree)
    return AST

def calculateInitState(code,varmap):
    AST = parseAST(code,varmap)    
    annotateTypes(AST)
    populateIStateMap(varmap,AST)
    return genInitTemplate()

def testFixPoint():
    a= [1,2,3,4,5,6]
    def f(l):
        if sum(a) > 10:
            l = l.pop()
        return l
    print(fixpoint(a,f))
if __name__ == '__main__':
    test(code2)
