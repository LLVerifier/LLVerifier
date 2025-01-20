#!/bin/python3
import re

def fixDot(code,changeLine=True):
    # Define the regex pattern for a rule and the "..." patterns
    # rule_pattern = r"((eq|rl)\s+((<.+?>)|(\$[^\=]+)|\s+)+(=>|=)\s+((<.+?>)|(\$[^\=]+)|\s+)+\s+\.(\s+|$))"
    #rule_pattern = r"((eq|rl)\s+(.+?)\s+(=>|=)\s+(.+?)\s+\.(\s+|$))"
    rule_pattern = r"((eq|rl)\s+([\S\s]+?)\s+(=>|=)\s+([\S\s]+?)\s+\.(\s+|$))"
    rules = re.findall(rule_pattern, code)
     
    transformed_rules = []
    
    for rule in rules:
        # Split the rule into the left and right parts of the '='
        delim = rule[3]
        left = ' '.join(rule[1:3])
        right = ' '.join(rule[4:])
        # Transform each side by replacing successive occurrences of "..."
        left = rename_dots(left)
        right = rename_dots(right)
        # Reconstruct the rule with the transformed sides
        if changeLine:
            transformed_rule = f"{left.strip()} \n {delim} {right.strip()} .\n"
        else:
            transformed_rule = f"{left.strip()} {delim} {right.strip()} .\n"
        transformed_rules.append(transformed_rule)
    # Replace original rules in the input code with transformed rules
    for original, transformed in zip([r[0] for r in rules], transformed_rules):
        code = code.replace(original, transformed)
    
    return code

def rename_dots(text):
    # Find all occurrences of "..."
    dots_positions = [(m.start(),m.end()) for m in re.finditer(r"\.\.\.\.*", text)]
    #print(dots_positions)
    # Replace each occurrence with increasing number of dots
    last_dots = [(0,0)]+dots_positions
    i = 0
    dn = 3
    size = len(text)
    result = ''
    for (ls,le),(ns,ne) in zip(last_dots,dots_positions+[(size,size)]):
        result += text[le:ns]
        if i < len(dots_positions):
            result += "."*dn
        i += 1
        dn += 1
    return result

def fixAt(code):
    rule_pattern = r"(rl\s+(.+?)\s*=>\s*(.+?)\s+\.(\s+|$))"
    rules = re.findall(rule_pattern, code)
    
    transformed_rules = []

    for rule in rules:
        left, right = rule[1],rule[2]
        transformed_rule = f'rl E @ S {left} \n=> ep: {right} @ S {left} .\n'
        transformed_rules.append(transformed_rule)
    for original, transformed in zip([r[0] for r in rules], transformed_rules):
        code = code.replace(original, transformed)
    
    return code

def test1():
    # Example usage
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
 = < cloudA | DeviceB : ('bdKey' : KeyC , 'owner' : false , ...) > .'''
    transformed_code = fixDot(code1)
    print(transformed_code)

def test2():
    code3 = '''\
rl < UserA | 'localTo' : false , 'know' : KeyA , ... > => ev6(UserA, deviceB, KeyA) .
rl < UserB | 'localTo' : false , 'know' : KeyA , ... > => ev8(UserB, deviceB, KeyA) .
rl < UserA | 'localTo' : DeviceB , 'know' : KeyA , ... > => ev4(UserA, DeviceB, KeyA) .
rl < UserA | 'localTo' : false , ... > => ev1(UserA, deviceB) .
rl < UserA | 'localTo' : DeviceB , ... > < UserA | 'localTo' : false , ... > => ev2(UserA, DeviceB) .
    '''
    print(fixDot(fixAt(code3)))

def test3():
    code = '''\
eq E @ S < cloudA | deviceB : ('owner' : userA, ...) , ... > |= uaowner = true .
eq E @ S < cloudA | deviceB : ('owner' : userC, ...) , ... > |= ucowner = true .
eq E @ S < userC | 'localTo' : deviceB, ... > |= uclocal = true .'''
    print(fixDot(code,False))

def test4():
    code = '''\
eq < cloudA | DeviceD : ('bdKey' : KeyX , 'owner' : OwnerU , ... ) , ... >
   $ UserU 'callAPI:reset' cloudA | (DeviceD ; KeyX)
= < cloudA | DeviceD : ('bdKey' : KeyX , 'owner' : nils , ... ) , ... > .
    '''
    print(fixDot(code))

def test5():
    code = '''\
rl < UserA | 'localTo' : DeviceB , ... > < DeviceB | ... > => ev2(UserA, DeviceB) .
rl < UserA | 'key' : KeyB , ... > < DeviceB | ... > < cloudA | DeviceB : ... , ... > => ev3(UserA, DeviceB, KeyB) .
rl < UserA | 'localTo' : DeviceB , ... > < DeviceB | ... > => $ UserA 'leave' DeviceB .
rl < UserA | 'localTo' : nils , ... > < DeviceB | ... > => ev1(UserA, DeviceB) .
    '''
    #print(fixDot(fixAt(code)))
    print(fixAt(fixDot(code)))

    #a = "rl < UserA | 'key' : KeyB , ... > < DeviceB | ... > < cloudA | DeviceB : ... , ... >"
    #a = "rl < UserA | 'key' : KeyB  >"
    #print(rename_dots(a))
if __name__ == '__main__':
    test5() 
