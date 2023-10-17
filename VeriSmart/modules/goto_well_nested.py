import pycparser.c_parser, pycparser.c_ast, pycparser.c_generator
import core.common, core.module, core.parser, core.utils
from collections import deque

class goto_well_nested(core.module.Translator):
    __gotos = [] # jumps that start from this statement (i.e., gotos)
    __labels = [] # labels in this statement (destinations) aka: closed labels
    __opens = dict() # maps each label l found so far with a pair (o, c) where o is the first "goto l;" found so far, and c is where the label was defined
    __goto_label_counter = 0 # count how many goto/labels found so far
    outermost_if_stack = None
    
    
    def jump_var_name(self, lbl):
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
        return self.jump_var_name(stmt.name)+" = 1;" #"goto "+stmt.name+";"
        
    def print_if_stack(self, label_closure_stack, enabled_closure_stack, skip_innermost=False, store_outermost=False):
        # print ifs for active variables according to the stack in reverse order
        n_ifs = 0
        conds = []
        for (active_jump_block, enabled_jumps) in zip(label_closure_stack, enabled_closure_stack):
            conds.append(" && ".join(["!"+self.jump_var_name(jmp) for (jmp, enabled) in zip(active_jump_block, enabled_jumps) if enabled]))
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
        orig_cond = cond
        this_labels += self.__labels
        this_gotos.update(self.__gotos)
        
        self.__labels = []
        self.__gotos = []
        then = self.visit(stmt.iftrue)
        this_labels += self.__labels
        this_gotos.update(self.__gotos)
            
        if len(self.__labels) > 0:
            cond = (" || ".join([self.jump_var_name(jmp) for jmp in self.__labels])) + " || "+cond
        
        if stmt.iffalse:
            then_gotos = set(self.__gotos)
            self.__labels = []
            self.__gotos = []
            els = self.visit(stmt.iffalse)
            this_labels += self.__labels
            this_gotos.update(self.__gotos)
            else_labels = set(self.__labels)
            else_header = "else "
            if len(self.__labels) > 0:
                cond = (" && ".join(["!"+self.jump_var_name(jmp) for jmp in self.__labels])) + " && ("+cond+")"
                if else_labels & then_gotos:
                    # jump from then to else
                    else_cond = (" || ".join([self.jump_var_name(jmp) for jmp in self.__labels])) + " || !("+orig_cond+")"
                    else_header = "if ("+else_cond+") "
            
        out += "if ("+cond+")"
        out += then
        if stmt.iffalse:
            out += else_header + els
        
        self.__labels = this_labels
        self.__gotos = list(this_gotos.difference(this_labels))
        return out
        
        
    def visit_Compound(self, stmt): #metti le jmpvar in uscita nel blocco piu' esterno, che copre tutto
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
        for s in stmt.block_items:
            self.__labels = []
            self.__gotos = []
            code_blocks.append(self.visit(s))
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
        out = "{\n"
        if_headers, nr_ifs = self.print_if_stack(label_closure_queue, enabled_closure_queue, skip_innermost=len(stmt.block_items)>0 and has_labels[0], store_outermost=len(stmt.block_items)>0 and type(stmt.block_items[0]) is pycparser.c_ast.If and not stmt.block_items[0].iffalse and (len(gotos_at[0]) > 0 or len(stmt.block_items) == 1))
        if self.outermost_if_stack is not None:
            code_blocks[0] = code_blocks[0].replace("if (", "if ("+self.outermost_if_stack+" && ", 1)
            self.outermost_if_stack = None
        out += if_headers
        for i in range(len(stmt.block_items)):
            if has_labels[i]: 
                #print("Has label", i, "popping", label_closure_queue[0])
                # close the currently open if block, such as anybody that needs to jump therein can do it
                # you just need to close the innermost if! Beware that if none of the labels are enabled, there's no if
                if any(enabled_closure_queue[0]) and i>0 and len(gotos_at[i-1]) == 0:
                    out += "}\n"
                    nr_ifs -= 1
                label_closure_queue.popleft()
                enabled_closure_queue.popleft()
                how_many_pops += 1
            out += code_blocks[i]+(";" if code_blocks[i] != ";" else "")+"\n"#+"// labels "+str(DEBUG_labels[i]) +" gotos "+str(gotos_at[i])+"\n"
            if i != len(stmt.block_items)-1 and len(gotos_at[i]) > 0:
                # there are gotos here, we should re-evaluate every jump variable starting from the outermost that might have changed TODO optimize 
                out += ("}"*nr_ifs+"\n") if nr_ifs > 0 else ""
                # set the jump vars as enabled
                for jmp in gotos_at[i]:
                    #print("GOTO", jmp)
                    if jmp not in where_is_label:
                        label_closure_queue[-1].append(jmp)
                        enabled_closure_queue[-1].append(True)
                        where_is_label[jmp] = [queue_max_size-1, len(label_closure_queue[0])-1]
                    else:
                        loc = where_is_label[jmp]
                        #print(jmp, loc, label_closure_queue, enabled_closure_queue, loc[0]-how_many_pops,loc[1], where_is_label, how_many_pops)
                        enabled_closure_queue[loc[0]-how_many_pops][loc[1]] = True
                        #print(enabled_closure_queue)
                if_headers, nr_ifs = self.print_if_stack(label_closure_queue, enabled_closure_queue, skip_innermost=has_labels[i+1], store_outermost=type(stmt.block_items[i+1]) is pycparser.c_ast.If and not stmt.block_items[i+1].iffalse and (len(gotos_at[i+1]) > 0 or len(stmt.block_items) == i+2))
                if self.outermost_if_stack is not None:
                    code_blocks[i+1] = code_blocks[i+1].replace("if (", "if ("+self.outermost_if_stack+" && ", 1)
                    self.outermost_if_stack = None
                out += if_headers
        out += ("}"*nr_ifs+"\n") if nr_ifs > 0 else ""
        self.__labels = this_labels
        self.__gotos = list(this_gotos.difference(this_labels))
        return out + "}\n"
        
    def visit_FuncDef(self, n):
        self.__opens = dict() 
        self.__goto_label_counter = 0
        decl = self.visit(n.decl)
        self.indent_level = 0
        body = self.visit(n.body)
        if len(self.__labels) > 0:
            jmp_decls = "static _Bool "+(", ".join([self.jump_var_name(jmp) for jmp in self.__labels]))+";\n"
            body = body.replace("{", "{"+jmp_decls, 1)
        if n.param_decls:
            knrdecls = ';\n'.join(self.visit(p) for p in n.param_decls)
            return decl + '\n' + knrdecls + ';\n' + body + '\n'
        else:
            return decl + '\n' + body + '\n'
        
