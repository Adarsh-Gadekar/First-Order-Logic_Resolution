import copy
class PredicateObjects:
    def __init__(self,predicate):
        indexOfOpen = predicate.index('(')
        indexOfClose = predicate.index(')')
        if predicate[0] == '~':
            self.bool = False
            self.literal = predicate[1:indexOfOpen]
        else:
            self.bool = True
            self.literal = predicate[0:indexOfOpen]
        if ',' in predicate[indexOfOpen+1:indexOfClose]:
            listOfParameters = predicate[indexOfOpen+1:indexOfClose].split(',')
            for i in range(len(listOfParameters)):
                listOfParameters[i] = listOfParameters[i].strip()
            self.parameters = listOfParameters
        else:
            l = []
            l.append(predicate[indexOfOpen+1:indexOfClose].strip())
            self.parameters = l
    
    def __lt__(self,other):
        if self.literal != other.literal:
            return self.literal < other.literal
        else:
            for arg1, arg2 in zip(self.parameters, other.parameters):
                if arg1[0].islower() and arg2[0].isupper():
                    return self.parameters < other.parameters
                elif arg1[0].isupper() and arg1[0].islower():
                    return self.parameters < other.parameters
                elif arg1[0].isupper() and arg2[0].isupper():
                    if arg1 != arg2:
                        return arg1 < arg2
        return self.bool < other.bool

    def __eq__(self, other):
        if isinstance(other, PredicateObjects):
            return (self.literal == other.literal and
                    self.parameters == other.parameters and
                    self.bool == other.bool)
        return False

def compareArgs(args1,args2):
    # if it is (variable,variable),(constant,variable),(variable,constant) no problem!
    # BUT if it is (constant,constant) then check of both of them are same if not return False
    for i in range(len(args1)):
        if args1[i][0].isupper() and args2[i][0].isupper() and args1[i] != args2[i]:
            return False
    return True

def resolve(clause1,clause2):

    for i in range(len(clause1)):
        for j in range(len(clause2)):
            #if the literals in both the clauses are same with different boolean values compare parameters
            if clause1[i].literal == clause2[j].literal and clause1[i].bool != clause2[j].bool:
                same_arguments = compareArgs(clause1[i].parameters,clause2[j].parameters)
                # if the arguments are similar i.e(var,var)/(const,var)/(var,const)/(same_const,same,const)
                if same_arguments:
                    return True,i,j
    return False,-1,-1

def removeDuplicates(resolvant):
    unique_predicate_list = []

    for predicate in resolvant:
        # check if the Predicate is not already in the unique list
        if predicate not in unique_predicate_list:
            unique_predicate_list.append(predicate)
    
    return unique_predicate_list

def doreplacement(list1,list2,d):
    for i in range(len(list1)):
        if list1[i] in d:
            list1[i] = d[list1[i]]

    for i in range(len(list2)):
        if list2[i] in d:
            list2[i] = d[list2[i]]

def unification(clause1,clause2,pos1,pos2):
    copy_clause1 = copy.deepcopy(clause1)
    copy_clause2 = copy.deepcopy(clause2)
    replace_dict={}
    resolvant = []
    args1 = copy_clause1[pos1].parameters
    args2 = copy_clause2[pos2].parameters

    for i in range(len(args1)):
        if args1[i][0].islower() and args2[i][0].islower():
            replace_dict[args2[i]]=args1[i]
            doreplacement(args1,args2,replace_dict)
        elif args1[i][0].islower() and args2[i][0].isupper():
            replace_dict[args1[i]] = args2[i]
            doreplacement(args1,args2,replace_dict)
        elif args1[i][0].isupper() and args2[i][0].islower():
            replace_dict[args2[i]]=args1[i]
            doreplacement(args1,args2,replace_dict)
        elif args1[i][0].isupper() and args2[i][0].isupper() and args1[i] != args2[i]:
            return False,[]

    if args1 != args2:
        return False,[]

    if bool(replace_dict):
        for key,val in replace_dict.items():
            if val in replace_dict:
                replace_dict[key] = replace_dict[val]
    
        # Changes in the parameters in the predicates of copy_clause1
        for i in range(len(copy_clause1)):
            p = copy_clause1[i].parameters
            for j in range(len(p)):
                if p[j] in replace_dict:
                    p[j] = replace_dict[p[j]]

        # Changes in the parameters in the predicates of copy_clause2
        for i in range(len(copy_clause2)):
            p = copy_clause2[i].parameters
            for j in range(len(p)):
                if p[j] in replace_dict:
                    p[j] = replace_dict[p[j]]
    
    for i in range(len(copy_clause1)):
        if i!=pos1:
            resolvant.append(copy_clause1[i])
    
    for i in range(len(copy_clause2)):
        if i!=pos2:
            resolvant.append(copy_clause2[i])

    resolvant = removeDuplicates(resolvant)
    resolvant.sort()
    return True,resolvant
        
def unify(clause1,clause2,pos1,pos2):
    resolvant = []
    unification_set = {}
    listOfParameters1 = clause1[pos1].parameters
    listOfParameters2 = clause2[pos2].parameters

    # Getting the dictonary of what to replace with what
    for i in range(len(listOfParameters1)):
            if listOfParameters1[i][0].islower() and listOfParameters2[i][0].islower():
                unification_set[listOfParameters1[i]] = listOfParameters2[i]
            elif listOfParameters1[i][0].islower() and listOfParameters2[i][0].isupper():
                unification_set[listOfParameters1[i]] = listOfParameters2[i]
            elif listOfParameters1[i][0].isupper() and listOfParameters2[i][0].islower():
                unification_set[listOfParameters2[i]] = listOfParameters1[i]
    
    copy_clause1 = copy.deepcopy(clause1)
    copy_clause2 = copy.deepcopy(clause2)

    # Changes in the parameters in the predicates of copy_clause1
    for i in range(len(copy_clause1)):
        p = copy_clause1[i].parameters
        for j in range(len(p)):
            if p[j] in unification_set:
                p[j] = unification_set[p[j]]

    # Changes in the parameters in the predicates of copy_clause2
    for i in range(len(copy_clause2)):
        p = copy_clause2[i].parameters
        for j in range(len(p)):
            if p[j] in unification_set:
                p[j] = unification_set[p[j]]
    
    for i in range(len(copy_clause1)):
        if i!=pos1:
            resolvant.append(copy_clause1[i])
    
    for i in range(len(copy_clause2)):
        if i!=pos2:
            resolvant.append(copy_clause2[i])
    resolvant.sort()

    #Resolvant can be empty or larger than or equal to the largest clause or smaller than the largest clause
    return resolvant

#Check if the clauses have same literals and Boolean values
def checkLiteralBool(clause1,clause2):
    for i in range(len(clause1)):
        if clause1[i].literal != clause2[i].literal:
            return False
        elif clause1[i].literal == clause2[i].literal and clause1[i].bool != clause2[i].bool:
            return False
    return True

#Check if the clauses with same literals and boolean have same parameters or not
def checkParameters(clause1,clause2):
    for i in range(len(clause1)):
        args1 = clause1[i].parameters
        args2 = clause2[i].parameters
        for j in range(len(args1)):
            if args1[j][0].islower() and args2[j][0].isupper():
                return False
            elif args1[j][0].isupper() and args2[j][0].islower():
                return False
            elif args1[j][0].isupper() and args2[j][0].isupper() and args1[j] != args2[j]:
                return False
    return True

def checkIfInKb(resolvant,kb):
    # Parse through clauses
    for i in range(len(kb)):
        # select a clause
        clause = kb[i]
        #check if length of the clause is same as length of resolvant
        if len(clause) == len(resolvant):
            # if yes then check if both clauses have same literals and boolean
            ans1 = checkLiteralBool(clause,resolvant)
            if ans1:
                # if yes then check if both clauses have same Predicates arguments
                ans2 = checkParameters(clause,resolvant)
                if ans2:
                # if yes then say the resolvant is in KB
                    return True
    return False
                                        
def std_resolvant(resolvant,i):
    count=1
    variable_dict = {}
    for j in range (len(resolvant)):
            parList = resolvant[j].parameters
            for k in range(len(parList)):
                if parList[k][0].islower() and parList[k] not in variable_dict:
                    variable_dict[parList[k]] = count
                    count = count+1
                    parList[k] = 'v'+'_'+str(i-1)+'_'+str(variable_dict[parList[k]])
                elif parList[k][0].islower() and parList[k] in variable_dict:
                    parList[k] = 'v'+'_'+str(i-1)+'_'+str(variable_dict[parList[k]])
                else:
                    continue

def resolution(kb):

    i=0
    l = len(kb)
    while(i<l):
    # We do the combination of clauses 
        clause1 = kb[i]
        j=0
        while(j<l):
            if i!=j:
                clause2 = kb[j]
                #We select 2 clauses and check if they both are resolvable
                #If they are resolvable then we know at which positions are the predicates which are gonna nullify
                resolvable,pos1,pos2 = resolve(clause1,clause2)
                if resolvable:
                    isUnifiable, resolvant = unification(clause1,clause2,pos1,pos2)
                    if isUnifiable and len(resolvant) == 0:
                        with open('output.txt','w') as f:
                            f.write("TRUE")
                            return
                    elif isUnifiable:
                        m = max(len(clause1),len(clause2))
                        if len(resolvant)<m:
                            ans = checkIfInKb(resolvant,kb)
                            if not ans:
                                std_resolvant(resolvant,len(kb))
                                resolvant.sort()
                                kb.append(resolvant)
            j+=1
            l = len(kb)
        i+=1
        l= len(kb)
            
    with open('output.txt','w') as f:
        f.write("FALSE")
        return

def standardize(kb):
    for i in range (len(kb)):
        clause = kb[i]
        count=1
        variable_dict = {}
        for j in range (len(clause)):
            parList = clause[j].parameters
            for k in range(len(parList)):
                if parList[k][0].islower() and parList[k] not in variable_dict:
                    variable_dict[parList[k]] = count
                    count = count+1
                    parList[k] = 'v'+'_'+str(i)+'_'+str(variable_dict[parList[k]])
                elif parList[k][0].islower() and parList[k] in variable_dict:
                    parList[k] = 'v'+'_'+str(i)+'_'+str(variable_dict[parList[k]])
                else:
                    continue
    # The KB is Standardized and the aruguments are set as v_lineNumber_argNumber 
    for sentence in kb:
        #KB is being sorted based on literal name,parameter list, boolean value
        sentence.sort()
    # Now the KB is ready for resolution
    resolution(kb)
    
#List of sentences and sentences here are list of Predicate Objects
def convertKB_objects(kb):
    new_kb = []
    for clause in kb:
        sentence = []
        if '|' in clause:
            listOfPredicates = clause.split('|')
            for predicate in listOfPredicates:
                p = PredicateObjects(predicate.strip())
                sentence.append(p)
            new_kb.append(sentence)
        else:
            p = PredicateObjects(clause)
            l = []
            l.append(p)
            new_kb.append(l)
    #[[P1,P2,P3],[P4,P5]] List of List of Predicates where Predicates have
    # ~Audi(Restaurant,x,y,Bar)
    # literal => string (Audi)
    # bool => True/False (False)
    # parameters => List of strings (['Restaurant','x','y','Bar'])
    # Then it is given to standardize
    standardize(new_kb)
            
#List of Sentences where sentences are List of Predicates as strings
def cnf(query,kb):
    for i in range(len(kb)):
        if("=>" in kb[i]):
            current = kb[i].split()
            cnf = ""
            for j in range(len(current)):
                if current[j] == "&":
                    current[j] = "|"
                elif current[j] == "=>":
                    current[j] = "|"
                    break
                else:
                    if(current[j][0] == '~'):
                        current[j] = current[j][1:]
                    else:
                        current[j] = '~'+current[j]
            cnf = ' '.join(current)
            kb[i] = cnf
        else:
            continue
    kb.append("~"+query)
    convertKB_objects(kb)   

def rhs_split_kb(query,kb):
    new_kb = []
    for sentence in kb:
        if '=>' in sentence:
            index_of_implication = sentence.index('=>')
            part_A = sentence[:index_of_implication].strip()
            part_B = sentence[index_of_implication+2:].strip()

            if '&' in part_B:
                l = part_B.split('&')
                for sen in l:
                    new_kb.append(part_A+" "+"=>"+" "+sen.strip())
            else:
                new_kb.append(sentence)
        else:
            new_kb.append(sentence)
    cnf(query,new_kb)
    # print(new_kb)
    
def lhs_split_kb(query,kb):
    new_kb = []
    for sentence in kb:
        if '=>' in sentence:
            index_of_implication = sentence.index('=>')
            part_A = sentence[:index_of_implication].strip()
            part_B = sentence[index_of_implication+2:].strip()

            if '|' in part_A:
                l = part_A.split('|')
                for sen in l:
                    new_kb.append(sen.strip()+" "+"=>"+" "+part_B)
            else:
                new_kb.append(sentence)
        else:
            if '&' in sentence:
                current = sentence.split('&')
                for word in current:
                    new_kb.append(word.strip())
            else:
                new_kb.append(sentence)
    rhs_split_kb(query,new_kb)
    # print(new_kb)
    
def main():

    #Taking Input
    with open("input.txt",'r') as f:
        query = f.readline().strip()
        num_sen_kb = int(f.readline())
        kb = []
        for line in f:
            kb.append(line.strip())

    lhs_split_kb(query,kb)
        
if __name__ == "__main__":
    main()