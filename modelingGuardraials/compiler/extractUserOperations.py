#!/bin/python3
from calculateInitState import parseAST,ASTVisitor,EVENT,PRINCIPAL,VARIABLE,LIST

# Example of parsing an IoT-Logic rule
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
eq < UserA | 'localTo' : DeviceB , ... > < UserB | 'localTo' : ItemA , ... > $ UserB 'approach' UserA
 = < UserA | 'localTo' : DeviceB , ... > < UserB | 'localTo' : DeviceB , ... > .
'''

class eventExtractor(ASTVisitor):
    def __init__(self):
        super().__init__()
        self.result = []
    def visitInternalState(self,i):
        if isinstance(i,EVENT):
            if i not in self.result:
                self.result.append(i)
        return self

def extractEvents(code,varmap):
    AST = parseAST(code,varmap)
    v = eventExtractor()
    v.visit(AST)
    return list(v.result)

def toDeclTxt(es):
    idx = 1
    l = []
    def helper(args:'LIST',params_lst):
        for arg in args.v:
            if isinstance(arg,VARIABLE):
                params_lst.append(arg.ident)
            elif isinstance(arg, LIST):
                helper(arg,params_lst)
    for e in es:
        params_lst = []
        if e.subject.ident[0].isupper():
            params_lst.append(e.subject.ident)
        if e.object.ident[0].isupper():
            params_lst.append(e.object.ident)
        if e.arguments:
            helper(e.arguments,params_lst) 
        params = ', '.join(params_lst)
        l.append(f'eq ev{idx}({params}) = '+str(e)+' .')
        idx += 1
    return '\n'.join(l)

if __name__ == '__main__':
    varmap = {'DeviceB':'Device','UserA':'User','UserD':'User','KeyC':'Qid','KeyD':'Qid','KeyE':'Qid','ItemA':'Item','UserB':'User'}
    varmap2 = {'UserA': 'User', 'DeviceB': 'Device', 'DeviceX': 'Device', 'CloudA': 'Cloud', 'KeyA': 'Qid', 'KeyB': 'Qid'}
    print(toDeclTxt(extractEvents(code1,varmap)))
