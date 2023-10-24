import pycparser.c_parser, pycparser.c_ast, pycparser.c_generator
import core.common, core.module, core.parser, core.utils
from collections import deque

class JumpBlock:
    def __init__(self, parent, cond):
        self.parent = parent
        self.cond = cond
        self.code_blocks = []
        self.cbs_type = [] # for each code_block: "S" regular statement, "J" JumpBlock, "I" if, "E" empty
        self.all_empty = True
        self.numJ = 0
        self.all_jump_empty = True
        self.numI = 0
        self.all_if_empty = True
        self.decls = []
    
    def add_statement(self, cb, typ):
        self.code_blocks.append(cb)
        self.cbs_type.append(typ)
        if typ != "E":
            self.all_empty = False
        if typ == "J":
            self.numJ += 1
        if typ == "I":
            self.numI += 1
        if typ not in ("J", "E"):
            self.all_jump_empty = False
        if typ not in ("I", "E"):
            self.all_if_empty = False
            
    def add_decl(self, cb):
        self.decls.append(cb)
        
    def output(self):
        out = "{\n" + "".join(d+";\n" for d in self.decls)
        if self.all_empty:
            return out+"\n".join(self.code_blocks)+"}"
        if self.all_jump_empty and self.numJ == 1:
            for i in range(len(self.code_blocks)):
                if self.cbs_type[i] == "E":
                    out += self.code_blocks[i] + "\n"
                elif self.cbs_type[i] == "J":
                    self.code_blocks[i].cond.extend(self.cond)
                    out += self.code_blocks[i].output() + "\n"
                else:
                    assert False
            return out+"}"
        if self.all_if_empty and self.numI == 1:
            for i in range(len(self.code_blocks)):
                if self.cbs_type[i] == "E":
                    out += self.code_blocks[i] + "\n"
                elif self.cbs_type[i] == "I":
                    if len(self.cond) == 0:
                        out += self.code_blocks[i] + "\n"
                    else:
                        this_cond = " && ".join("("+c+")" for c in self.cond[::-1])
                        out += self.insert_in_if(self.code_blocks[i], this_cond) + "\n"
                else:
                    assert False
            return out+"}"
        #default case
        if len(self.cond) > 0:
            out = "if ("+" && ".join("("+c+")" for c in self.cond[::-1])+")"+out
        for i in range(len(self.code_blocks)):
            if self.cbs_type[i] == "J":
                out += self.code_blocks[i].output() + "\n"
            elif self.cbs_type[i] in ("E", "I"):
                out += self.code_blocks[i] + "\n"
            else:
                out += self.code_blocks[i] + ";\n"
        return out+"}"
        
    def insert_in_if(self, code, cnd):
        out = ""
        i = 0
        while code[i:i+4] != "if (":
            out += code[i]
            i += 1
        out += code[i:i+3]
        i+=3
        brackets = 1
        cond = code[i]
        i+=1
        while brackets > 0:
            cond += code[i]
            if code[i] == "(":
                brackets += 1
            elif code[i] == ")":
                brackets -= 1
            i += 1
        out += "("+cnd+" && "+cond+")"
        out += code[i:]
        return out
        
class CompoundJumpBlockBuilder:
    def __init__(self):
        self.root = JumpBlock(None, [])
        self.where_to_add = self.root
        
    def add_if_stack(self, label_closure_stack, enabled_closure_stack):
        # print ifs for active variables according to the stack in reverse order
        n_ifs = 0
        conds = []
        for (active_jump_block, enabled_jumps) in zip(label_closure_stack, enabled_closure_stack):
            conds.append(" && ".join(["!("+goto_well_nested.jump_var_name(jmp)+")" for (jmp, enabled) in zip(active_jump_block, enabled_jumps) if enabled]))
        # in reverse
        for cond in conds[::-1]:
            if len(cond) > 0:
                jblock = JumpBlock(self.where_to_add, [cond])
                self.where_to_add.add_statement(jblock, "J")
                self.where_to_add = jblock
                n_ifs += 1
        return n_ifs
        
    def close_ifs(self, nr_ifs):
        for i in range(nr_ifs):
            self.where_to_add = self.where_to_add.parent
            
    def add(self, code, item):
        while type(item) == pycparser.c_ast.Label:
            item = item.stmt
        if type(item) is pycparser.c_ast.Decl:
            self.root.add_decl(code)
        else:
            tp = "S"
            if type(item) is pycparser.c_ast.If:
                tp = "I"
            elif type(item) is pycparser.c_ast.EmptyStatement:
                tp = "E"
            self.where_to_add.add_statement(code, tp)
        
    def compile(self):
        assert self.root == self.where_to_add
        return self.root.output()
        
        
            

class goto_well_nested(core.module.Translator):
    __gotos = [] # jumps that start from this statement (i.e., gotos)
    __labels = [] # labels in this statement (destinations) aka: closed labels
    __opens = dict() # maps each label l found so far with a pair (o, c) where o is the first "goto l;" found so far, and c is where the label was defined
    __goto_label_counter = 0 # count how many goto/labels found so far
    outermost_if_stack = None
    next_statement_stk = deque()
    needs_label = set()
    
    @staticmethod
    def jump_var_name(lbl):
        return "__cs_jmp_"+lbl
    
    def visit_Label(self, stmt):
        self.__labels.append(stmt.name)
        if stmt.name in self.__opens: # somebody references this label
            lbl_text = stmt.name+": "
            self.__opens[stmt.name][1] = self.__goto_label_counter
            self.__goto_label_counter += 1
            return lbl_text + self.visit(stmt.stmt)
        else:
            self.__opens[stmt.name] = [None, self.__goto_label_counter]
            self.__goto_label_counter += 1
            return self.visit(stmt.stmt)
        
    def visit_Goto(self, stmt):
        self.__gotos.append(stmt.name)
        if stmt.name in self.__opens: # not a new label
            if self.__opens[stmt.name][1] is not None:
                # Jumping back!!! Forbidden
                print("ERR", stmt.name)
                assert(False)
        else: # first time this label is referenced
            self.__opens[stmt.name] = [self.__goto_label_counter, None]
        self.__goto_label_counter += 1
        needs_label_here = True
        if stmt.name not in self.needs_label and len(self.next_statement_stk)>0:
            nxt_stmt = self.next_statement_stk[-1]
            while needs_label_here and type(nxt_stmt) is pycparser.c_ast.Label:
                if nxt_stmt.name == stmt.name:
                    needs_label_here = False
                nxt_stmt = nxt_stmt.stmt
            if needs_label_here:
                self.needs_label.add(stmt.name)
        if needs_label_here:
            return goto_well_nested.jump_var_name(stmt.name)+" = 1" #"goto "+stmt.name+";"
        else:
            return ";"
        
    def print_if_stack(self, label_closure_stack, enabled_closure_stack, skip_innermost=False, store_outermost=False):
        # print ifs for active variables according to the stack in reverse order
        n_ifs = 0
        conds = []
        for (active_jump_block, enabled_jumps) in zip(label_closure_stack, enabled_closure_stack):
            conds.append(" && ".join(["!("+goto_well_nested.jump_var_name(jmp)+")" for (jmp, enabled) in zip(active_jump_block, enabled_jumps) if enabled]))
        self.outermost_if_stack = None
        start = len(conds) - 1
        while store_outermost and start >= 0 and self.outermost_if_stack is None:
            if len(conds[start]) > 0:
                self.outermost_if_stack = conds[start]
            start -= 1
        # in reverse
        out = ""
        end = 0 if skip_innermost else None
        for cond in conds[start:end:-1]:
            if len(cond) > 0:
                out += "if("+cond+"){"
                n_ifs += 1
        return out + "\n", n_ifs
        
    def visit_If(self, stmt):
        #print("IF", stmt.cond)
        out = ""
        self.__labels = []
        self.__gotos = []
        this_labels = []
        this_gotos = set()
        cond = self.visit(stmt.cond)
        glc_start = self.__goto_label_counter # see which jumps were open when compound begins
        orig_cond = cond
        this_labels += self.__labels
        this_gotos.update(self.__gotos)
        
        self.__labels = []
        self.__gotos = []
        then = self.visit(stmt.iftrue)
        this_labels += self.__labels
        this_gotos.update(self.__gotos)
        
        open_then = [l for l in self.__labels if l in self.__opens and self.__opens[l][0] is not None and self.__opens[l][0] < glc_start] # enabled at compound begin time
            
        if len(open_then) > 0:
            cond = (" || ".join(["("+goto_well_nested.jump_var_name(jmp)+")" for jmp in open_then])) + " || ("+cond+")"
        
        if stmt.iffalse:
            then_gotos = set(self.__gotos)
            self.__labels = []
            self.__gotos = []
            else_start = self.__goto_label_counter # see which jumps were open when else begins
            els = self.visit(stmt.iffalse)
            this_labels += self.__labels
            this_gotos.update(self.__gotos)
            else_labels = set(self.__labels)
            else_header = "else "
            open_else = [l for l in self.__labels if l in self.__opens and self.__opens[l][0] is not None and self.__opens[l][0] < else_start] # enabled at compound begin time
            if len(open_else) > 0:
                cond = (" && ".join(["!("+goto_well_nested.jump_var_name(jmp)+")" for jmp in open_else])) + " && ("+cond+")"
                if else_labels & then_gotos:
                    # jump from then to else
                    else_cond = (" || ".join(["("+goto_well_nested.jump_var_name(jmp)+")" for jmp in open_else])) + " || !("+orig_cond+")"
                    else_header = "if ("+else_cond+") "
            
        out += "if ("+cond+")"
        out += then
        if stmt.iffalse:
            out += else_header + els
        
        self.__labels = this_labels
        self.__gotos = list(this_gotos.difference(this_labels))
        return out
        
    def insert_outermost_in_if(self, code):
        out = ""
        i = 0
        while code[i:i+4] != "if (":
            out += code[i]
            i += 1
        out += code[i:i+3]
        i+=3
        brackets = 1
        cond = code[i]
        i+=1
        while brackets > 0:
            cond += code[i]
            if code[i] == "(":
                brackets += 1
            elif code[i] == ")":
                brackets -= 1
            i += 1
        out += "("+self.outermost_if_stack+" && "+cond+")"
        out += code[i:]
        return out
        
    def visit_Compound(self, stmt): #metti le jmpvar in uscita nel blocco piu' esterno, che copre tutto
        if stmt.block_items is not None:
            cmpb = CompoundJumpBlockBuilder()
            this_labels = []
            this_gotos = set()
            label_closure_queue = deque() # queue that contains closed labels. Earlier closures require a more nested if
            enabled_closure_queue = deque()
            glc_start = self.__goto_label_counter # see which jumps were open when compound begins
            how_many_pops = 0
            queue_max_size = 0
            where_is_label = dict()
            code_blocks = []
            has_labels = []
            DEBUG_labels = []
            gotos_at = []
            s_nxt = 0 # index of the first statement in the block that isn't an EmptyStatement
            for s_i, s in enumerate(stmt.block_items):
                self.__labels = []
                self.__gotos = []
                if s_i >= s_nxt:
                    s_nxt = s_i + 1
                    while s_nxt < len(stmt.block_items) and type(stmt.block_items[s_nxt]) is pycparser.c_ast.EmptyStatement:
                        s_nxt += 1
                    if s_nxt < len(stmt.block_items):
                        self.next_statement_stk.append(stmt.block_items[s_nxt])
                code_blocks.append(self.visit(s))
                if s_i+1 >= s_nxt and s_nxt < len(stmt.block_items):
                    self.next_statement_stk.pop()
                this_gotos.update(self.__gotos)
                gotos_at.append(self.__gotos)
                has_labels.append(len(self.__labels) > 0)
                DEBUG_labels.append(self.__labels)
                if has_labels[-1]:
                    #print("Found labels: ", self.__labels)
                    this_labels += self.__labels
                    label_closure_queue.append(self.__labels)
                    lcnt = 0
                    ecs_element = []
                    enabled_closure_queue.append(ecs_element)
                    for l in self.__labels:
                        where_is_label[l] = [queue_max_size, lcnt]
                        ecs_element.append(l in self.__opens and self.__opens[l][0] is not None and self.__opens[l][0] < glc_start) # enabled at compound begin time
                        lcnt += 1
                    queue_max_size += 1
            # last queue block is reserved for goto labels not closed in this compound. Will be filled fater each goto happens
            label_closure_queue.append([])
            enabled_closure_queue.append([])
            queue_max_size += 1
            #######
            #print("LCS", label_closure_queue)
            #print("STK", enabled_closure_queue)
            #print("GOTOS", gotos_at)
            #print("".join(code_blocks))
            #out = "{\n"
            nr_ifs = cmpb.add_if_stack(label_closure_queue, enabled_closure_queue)
            #if_headers, nr_ifs = self.print_if_stack(label_closure_queue, enabled_closure_queue, skip_innermost=len(stmt.block_items)>0 and has_labels[0], store_outermost=len(stmt.block_items)>0 and type(stmt.block_items[0]) is pycparser.c_ast.If and not stmt.block_items[0].iffalse and (len(gotos_at[0]) > 0 or len(stmt.block_items) == 1))
            #if self.outermost_if_stack is not None:
            #    code_blocks[0] = self.insert_outermost_in_if(code_blocks[0])
            #    self.outermost_if_stack = None
            #out += if_headers
            for i in range(len(stmt.block_items)):
                if has_labels[i]: 
                    #print("Has label", i, "popping", label_closure_queue[0])
                    # close the currently open if block, such as anybody that needs to jump therein can do it
                    # you just need to close the innermost if! Beware that if none of the labels are enabled, there's no if
                    if any(enabled_closure_queue[0]):# and i>0 and len(gotos_at[i-1]) == 0:
                        #out += "}\n"
                        cmpb.close_ifs(1)
                        nr_ifs -= 1
                    label_closure_queue.popleft()
                    enabled_closure_queue.popleft()
                    how_many_pops += 1
                #if type(stmt.block_items[i]) is pycparser.c_ast.Decl:
                #    #out += ("}"*nr_ifs+"\n") if nr_ifs > 0 else ""
                #    cmpb.close_ifs(nr_ifs)
                #    nr_ifs = 0
                cmpb.add(code_blocks[i], stmt.block_items[i])
                #out += code_blocks[i]+(";" if code_blocks[i] != ";" else "")+"\n"#+"// labels "+str(DEBUG_labels[i]) +" gotos "+str(gotos_at[i])+"\n"
                if i != len(stmt.block_items)-1 and (len(gotos_at[i]) > 0): #or type(stmt.block_items[i]) is pycparser.c_ast.Decl):
                    # there are gotos here, we should re-evaluate every jump variable starting from the outermost that might have changed TODO optimize 
                    #out += ("}"*nr_ifs+"\n") if nr_ifs > 0 else ""
                    cmpb.close_ifs(nr_ifs)
                    # set the jump vars as enabled
                    for jmp in gotos_at[i]:
                        #print("GOTO", jmp)
                        if jmp not in where_is_label:
                            label_closure_queue[-1].append(jmp)
                            enabled_closure_queue[-1].append(True)
                            where_is_label[jmp] = [queue_max_size-1, len(label_closure_queue[-1])-1]
                        else:
                            loc = where_is_label[jmp]
                            assert(label_closure_queue[loc[0]-how_many_pops][loc[1]] == jmp)
                            #print(jmp, loc, label_closure_queue, enabled_closure_queue, loc[0]-how_many_pops,loc[1], where_is_label, how_many_pops)
                            enabled_closure_queue[loc[0]-how_many_pops][loc[1]] = True
                            #print(enabled_closure_queue)
                    #if_headers, nr_ifs = self.print_if_stack(label_closure_queue, enabled_closure_queue, skip_innermost=has_labels[i+1], store_outermost=type(stmt.block_items[i+1]) is pycparser.c_ast.If and not stmt.block_items[i+1].iffalse and (len(gotos_at[i+1]) > 0 or len(stmt.block_items) == i+2))
                    #if self.outermost_if_stack is not None:
                    #    code_blocks[i+1] = self.insert_outermost_in_if(code_blocks[i+1])
                    #    self.outermost_if_stack = None
                    nr_ifs = cmpb.add_if_stack(label_closure_queue, enabled_closure_queue)
                    #out += if_headers
            #out += ("}"*nr_ifs+"\n") if nr_ifs > 0 else ""
            cmpb.close_ifs(nr_ifs)
            self.__labels = this_labels
            self.__gotos = list(this_gotos.difference(this_labels))
            #out += cmpb.compile()
            return cmpb.compile()
            #return out + "}\n"
        else:
            self.__labels = set()
            self.__gotos = []
            return "{\n}\n"
        
    def visit_FuncDef(self, n):
        self.__opens = dict() 
        self.__goto_label_counter = 0
        self.needs_label = set()
        decl = self.visit(n.decl)
        self.indent_level = 0
        body = self.visit(n.body)
        jmp_decls = "static _Bool "+(", ".join([goto_well_nested.jump_var_name(jmp) for jmp in self.__labels if jmp in self.needs_label]))+";\n"
        if len(jmp_decls) > 15:
            body = body.replace("{", "{"+jmp_decls, 1)
        if n.param_decls:
            knrdecls = ';\n'.join(self.visit(p) for p in n.param_decls)
            return decl + '\n' + knrdecls + ';\n' + body + '\n'
        else:
            return decl + '\n' + body + '\n'
        

