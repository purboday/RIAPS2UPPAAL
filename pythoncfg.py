#!/usr/bin/env python3
# Author: Rahul Gopinath <rahul.gopinath@cispa.saarland>
# Modified by: Purboday Ghosh ,purboday.ghosh@vanderbilt.edu>
# License: https://github.com/uds-se/fuzzingbook/blob/master/LICENSE.md
"""
PyCFG for Python MCI
Use http://viz-js.com/ to view digraph output
"""

import ast
import horast
import re
import astunparse
import pygraphviz
import typed_ast.ast3 as tast
import random

from textx import metamodel_from_file
from textx.exceptions import TextXSyntaxError

class CFGNode(dict):
    registry = 0
    cache = {}
    stack = []
    def __init__(self, parents=[], ast=None):
        #assert type(parents) is list
        if type(parents) is tuple:
            self.kind = parents[1]
            self.parents = parents[0]
        else:
            self.kind = ''
            self.parents = parents
        self.calls = []
        self.children = []
        self.ast_node = ast
        self.rid  = CFGNode.registry
        CFGNode.cache[self.rid] = self
        CFGNode.registry += 1

    def lineno(self):
        return self.ast_node.lineno if hasattr(self.ast_node, 'lineno') else 0

    def __str__(self):
        x = self.kind
        return "id:%d line[%d] parents: %s : %s %s" % (self.rid, self.lineno(), str([p.rid for p in self.parents]), self.source(), x)

    def __repr__(self):
        return str(self)

    def add_child(self, c):
        if c not in self.children:
            self.children.append(c)

    def __eq__(self, other):
        return self.rid == other.rid

    def __neq__(self, other):
        return self.rid != other.rid

    def set_parents(self, p):
        self.parents = p

    def add_parent(self, p):
        if p not in self.parents:
            self.parents.append(p)

    def add_parents(self, ps):
        for p in ps:
            self.add_parent(p)

    def add_calls(self, func):
        self.calls.append(func)

    def source(self):
        return horast.unparse(self.ast_node).strip()

    def to_json(self):
        return {'id':self.rid, 'parents': [p.rid for p in self.parents], 'children': [c.rid for c in self.children], 'calls': self.calls, 'at':self.lineno() ,'ast':self.source()}


class PyCFG:
    """
    The python CFG
    """
    def __init__(self):
        self.founder = CFGNode(parents=[], ast=horast.parse('start').body[0]) # sentinel
        self.founder.ast_node.lineno = 0
        self.functions = {}
        self.functions_node = {}
        self.code_metadata = {}
        self.code_metadata['template']=''
        #self.code_metadata['global_variables']=[]
        self.code_metadata['local_variables']=[]
        self.code_metadata['locations'] = []
        self.code_metadata['committed'] = []
        self.code_metadata['edges']=[]
        self.code_metadata['specs']=[]
        self.auto_edges = []
        self.user_edges = []
        self.port_data = None
        self.origin = None
        self.metamodel = metamodel_from_file("templates/xtaspec.tx")

    def parse(self, src):
        return horast.parse(src)

    def walk(self, node, myparents):
        if node is None: return
        fname = "on_%s" % node.__class__.__name__.lower()
        #print(fname)
        # print(fname)
        if hasattr(self, fname):
            fn = getattr(self, fname)
            # print('fn')
            # print(fname)
            v = fn(node, myparents)
            return v
        else:
            return myparents
        
    def on_classdef(self, node, myparents):
        # print(ast.dump(node))
        if node.bases[0].id == 'Component':
            self.code_metadata['template'] = node.name
        p = [CFGNode(parents=[], ast=horast.parse('_class: %s' % node.name))]
        p[0].ast_node.lineno=node.lineno
        for c_method in node.body:
            p=self.walk(c_method, p)
        return myparents

    def on_module(self, node, myparents):
        """
        Module(stmt* body)
        """
        # each time a statement is executed unconditionally, make a link from
        # the result to next statement
        p = myparents
        for n in node.body:
            p = self.walk(n, p)
        return p

    def on_assign(self, node, myparents):
        """
        Assign(expr* targets, expr value)
        TODO: AugAssign(expr target, operator op, expr value)
        -- 'simple' indicates that we annotate simple name without parens
        TODO: AnnAssign(expr target, expr annotation, expr? value, int simple)
        """
        # print(ast.dump(node))
        if len(node.targets) > 1: raise NotImplemented('Parallel assignments')
        p = [CFGNode(parents=myparents, ast=node)]
        p = self.walk(node.value, p)
        r=self.walk(node.targets[0],myparents)

        return p

    def on_pass(self, node, myparents):
        return [CFGNode(parents=myparents, ast=node)]

    def on_break(self, node, myparents):
        parent = myparents[0]
        while not hasattr(parent, 'exit_nodes'):
            # we have ordered parents
            parent = parent.parents[0]

        assert hasattr(parent, 'exit_nodes')
        p = CFGNode(parents=myparents, ast=node)

        # make the break one of the parents of label node.
        parent.exit_nodes.append(p)

        # break doesnt have immediate children
        return []

    def on_continue(self, node, myparents):
        parent = myparents[0]
        while not hasattr(parent, 'exit_nodes'):
            # we have ordered parents
            parent = parent.parents[0]
        assert hasattr(parent, 'exit_nodes')
        p = CFGNode(parents=myparents, ast=node)

        # make continue one of the parents of the original test node.
        parent.add_parent(p)

        # return the parent because a continue is not the parent
        # for the just next node
        return []

    def on_for(self, node, myparents):
        #node.target in node.iter: node.body
        _test_node = CFGNode(parents=myparents, ast=horast.parse('_for: True if %s else False' % horast.unparse(node.iter).strip()).body[0])
        tast.copy_location(_test_node.ast_node, node)

        # we attach the label node here so that break can find it.
        _test_node.exit_nodes = []
        test_node = self.walk(node.iter, [_test_node])

        extract_node = CFGNode(parents=[_test_node], ast=ast.parse('%s = %s.shift()' % (horast.unparse(node.target).strip(), astunparse.unparse(node.iter).strip())).body[0])
        tast.copy_location(extract_node.ast_node, _test_node.ast_node)

        # now we evaluate the body, one at a time.
        p1 = [extract_node]
        for n in node.body:
            p1 = self.walk(n, p1)

        # the test node is looped back at the end of processing.
        _test_node.add_parents(p1)

        return _test_node.exit_nodes + (test_node, False)


    def on_while(self, node, myparents):
        # For a while, the earliest parent is the node.test
        # lbl1 node
        _test_node = CFGNode(parents=myparents, ast=horast.parse('_while: %s' % horast.unparse(node.test).strip()).body[0])
        tast.copy_location(_test_node.ast_node, node.test)
        _test_node.exit_nodes = []
        # p
        test_node = self.walk(node.test, [_test_node])

        # # we attach the label node here so that break can find it.
        #
        # # now we evaluate the body, one at a time.
        # p1 = (test_node, True)
        # for n in node.body:
        #     p1 = self.walk(n, p1)
        #
        # # the test node is looped back at the end of processing.
        # _test_node.add_parents(p1)
        #
        # # link label node back to the condition.
        # return _test_node.exit_nodes
        lbl2_node = CFGNode(parents=test_node, ast=node.test)
        g_false = CFGNode(parents=[lbl2_node], ast=horast.parse("_if:False"))
        g_true = CFGNode(parents=[lbl2_node], ast=horast.parse("_if:True"))
        _test_node.exit_nodes = [g_false]

        p = [g_true]

        for n in node.body:
            p = self.walk(n, p)

        # the last node is the parent for the lb1 node.
        _test_node.add_parents(p)

        return _test_node.exit_nodes


    def on_if(self, node, myparents):
        _test_node = CFGNode(parents=myparents, ast=horast.parse('_if: %s' % horast.unparse(node.test).strip()).body[0])
        tast.copy_location(_test_node.ast_node, node.test)
        test_node = self.walk(node.test, [_test_node])
        g1 = (test_node, True)
        for n in node.body:
            g1 = self.walk(n, g1)
        g2 = (test_node, False)
        for n in node.orelse:
            g2 = self.walk(n, g2)
        # treat no else as a simple pass    
        if len(node.orelse) == 0:
            g2 = self.on_pass(n, g2)
        return g1 + g2

    def on_binop(self, node, myparents):
        left = self.walk(node.left, myparents)
        # print(ast.dump(node))
        # print(node.left.__class__.__name__.lower())
        # print(node.left.value.id)
        right = self.walk(node.right, left)
        return right

    def on_compare(self, node, myparents):
        left = self.walk(node.left, myparents)
        right = self.walk(node.comparators[0], left)
        return right

    def on_unaryop(self, node, myparents):
        return self.walk(node.operand, myparents)
    
    def on_attribute(self, node, myparents):
        # if node.value.id == 'self':
        #     if node.attr not in self.code_metadata['local_variables'] and node.attr not in self.code_metadata['global_variables']:
        #         self.code_metadata['local_variables'].append(node.attr)
        return myparents
    
    def on_name(self, node, myparents):
        # if node.id not in self.code_metadata['local_variables'] and node.id not in self.code_metadata['global_variables']:
        #     self.code_metadata['local_variables'].append(node.id)
        return myparents

    def on_call(self, node, myparents):
        def get_func(node):
            if type(node.func) is tast.Name:
                mid = node.func.id
            elif type(node.func) is tast.Attribute:
                mid = node.func.attr
            elif type(node.func) is tast.Call:
                mid = get_func(node.func)
            else:
                raise Exception(str(type(node.func)))
            return mid
                #mid = node.func.value.id

        p = myparents
        for a in node.args:
            p = self.walk(a, p)
        mid = get_func(node)
        myparents[0].add_calls(mid)

        # these need to be unlinked later if our module actually defines these
        # functions. Otherwsise we may leave them around.
        # during a call, the direct child is not the next
        # statement in text.
        for c in p:
            c.calllink = 0
        return p

    def on_expr(self, node, myparents):
        p = [CFGNode(parents=myparents, ast=node)]
        return self.walk(node.value, p)

    def on_return(self, node, myparents):
        if type(myparents) is tuple:
            parent = myparents[0][0]
        else:
            parent = myparents[0]

        val_node = self.walk(node.value, myparents)
        # on return look back to the function definition.
        while not hasattr(parent, 'return_nodes'):
            parent = parent.parents[0]
        assert hasattr(parent, 'return_nodes')

        p = CFGNode(parents=val_node, ast=node)

        # make the break one of the parents of label node.
        parent.return_nodes.append(p)

        # return doesnt have immediate children
        return []

    def on_functiondef(self, node, myparents):
        # a function definition does not actually continue the thread of
        # control flow
        # name, args, body, decorator_list, returns
        fname = node.name
        args = node.args
        returns = node.returns
        
        # for class constructors, link it to the class definition since it is a special function.
        if node.name == '__init__':
            pt = myparents
            # add initial location "ready"
            #self.code_metadata['arguments'] =[a.arg for a in node.args.args if a.arg != 'self']
            self.code_metadata['locations'].append({'id': 'ready_%d' % node.lineno, 'init' : True })
            self.origin = 'ready_%d' %(node.lineno)
        else:
            pt = []
            # add method and handler locations
            #print(node.name+','+str(node.lineno))
            self.code_metadata['locations'].append({'id':'%s_%d' % (node.name, node.lineno)})
            self.code_metadata['committed'].append('%s_%d' % (node.name, node.lineno))
            self.code_metadata['locations'][-1]['commit'] = True
            if node.name.startswith('on_'):
                port_nm = node.name[3:]
                port_info = self.port_data[self.code_metadata['template']]['ports'][port_nm]
                if port_info['type'] == 'tim':
                    self.code_metadata['local_variables'].append({'name': 'period', 'type' : 'int' , 'value' : port_info['period']})
                for item in self.code_metadata['locations']:
                    if 'ready' in item['id']:
                        src = item['id']
                        break
                # add edges for handlers from the initial location
                self.code_metadata['edges'].append({'source': src, 'target':'%s_%s' % (node.name, node.lineno), 
                                                    'sync' : 'executehandler?',
                                                    'guard' : 'socket == %s_%s_q.id' % (self.code_metadata['template'],port_nm),
                                                    'assign' : "exec_time = 0"})
                # self.code_metadata['edges'].append({'source': '%s_%s' % (node.lineno,node.name), 'target': src })
            else:
                pass
                
        enter_node = CFGNode(parents=pt, ast=horast.parse('enter: %s(%s)' % (node.name, ', '.join([a.arg for a in node.args.args])) ).body[0]) # sentinel
        enter_node.calleelink = True
        tast.copy_location(enter_node.ast_node, node)
        exit_node = CFGNode(parents=[], ast=horast.parse('exit: %s(%s)' % (node.name, ', '.join([a.arg for a in node.args.args])) ).body[0]) # sentinel
        exit_node.fn_exit_node = True
        tast.copy_location(exit_node.ast_node, node)
        enter_node.return_nodes = [] # sentinel

        p = [enter_node]
        
        #print(node.name)
        for n in node.body:
            p = self.walk(n, p)
            if node.name.startswith('on_'):
                if n.__class__.__name__.lower() == "comment":
                    #print(n.comment)
                    try:
                        specs = self.metamodel.model_from_str(n.comment)
                        for ant in specs.annotations:
                            if ant.prop.__class__.__name__.lower()=="timing":
                                self.code_metadata["locations"].append({'id':'user_op_%d' % (n.lineno), 'inv' : 'exec_time <= %d' %(ant.prop.min*10), 'min' : ant.prop.min, 'max' : ant.prop.max})
                                #print('user_op_%d' %(n.lineno))
                    except TextXSyntaxError:
                        pass

        for n in p:
            if n not in enter_node.return_nodes:
                enter_node.return_nodes.append(n)

        for n in enter_node.return_nodes:
            exit_node.add_parent(n)

        self.functions[fname] = [enter_node, exit_node]
        self.functions_node[enter_node.lineno()] = fname

        return myparents

    def get_defining_function(self, node):
        if node.lineno() in self.functions_node: return self.functions_node[node.lineno()]
        if not node.parents:
            self.functions_node[node.lineno()] = ''
            return ''
        val = self.get_defining_function(node.parents[0])
        self.functions_node[node.lineno()] = val
        return val

    def link_functions(self):
        for nid,node in CFGNode.cache.items():
            if node.calls:
                for calls in node.calls:
                    # print(ast.dump(node.ast_node))
                    if calls in self.functions:
                        enter, exit = self.functions[calls]
                        enter.add_parent(node)
                        if node.children:
                            # # until we link the functions up, the node
                            # # should only have succeeding node in text as
                            # # children.
                            # assert(len(node.children) == 1)
                            # passn = node.children[0]
                            # # We require a single pass statement after every
                            # # call (which means no complex expressions)
                            # assert(type(passn.ast_node) == ast.Pass)

                            # # unlink the call statement
                            assert node.calllink > -1
                            node.calllink += 1
                            for i in node.children:
                                i.add_parent(exit)
                            # passn.set_parents([exit])
                            # ast.copy_location(exit.ast_node, passn.ast_node)


                            # #for c in passn.children: c.add_parent(exit)
                            # #passn.ast_node = exit.ast_node

    def update_functions(self):
        for nid,node in CFGNode.cache.items():
            _n = self.get_defining_function(node)

    def update_children(self):
        for nid,node in CFGNode.cache.items():
            #print(node)
            for p in node.parents:
                p.add_child(node)
                
    def add_ta_edges(self, calls, called, args=None):
        
        src = None
        dst = None
        # print('calls'+calls)
        # print('called'+called)
        for item in self.code_metadata['locations']:
            if calls in item['id']:
                dst = item['id']
            if called in item['id']:
                src = item['id']
            if src is not None and dst is not None:
                break
        found = False
        idx = -1
        if src is not None and dst is not None:
            for idx,edge in enumerate(self.code_metadata['edges']):
                if src in edge['source'] and dst in edge['target']:
                    found = True
                    break
            if not found:
                self.code_metadata['edges'].append({'source': src, 'target':dst})
                self.add_guards_syncs_outs(self.code_metadata['edges'][-1],args)
                # self.code_metadata['edges'].append({'source': dst, 'target':src})
                idx = idx + 1
        
        return idx
    
    def add_guards_syncs_outs(self,edge,args=None):
        
        # recv_pyobj() transitions
        if 'blocking' not in edge['source'] and 'pre_recv' in edge['target']:
            edge['assign'] = "status = pop(%s_%s_q)" %(self.code_metadata["template"],args['port'])
            
        elif 'pre_recv' in edge['source'] and 'post_recv' in edge['target']:
            edge['guard'] = "status >= 0"
            
        elif 'pre_recv' in edge['source'] and 'blocking' in edge['target']:
            edge['guard'] = "status < 0"
            
        elif 'blocking' in edge['source'] and 'pre_recv' in edge['target']:
            edge['sync'] = "go?"
            
        # send_pyobj() transitions
        
        elif 'post_send' in edge['target']:
            if args['attr']['type'] in ['pub','req','qry','clt']:
                edge['sync'] = "%s_channel!" %(args['attr']['msgtype'][0])
            else:
                edge['sync'] = "%s_channel!" %(args['attr']['msgtype'][1])
                
            if args['attr']['type'] in ['qry','ans']:
                edge['assign'] = "identity = %s_%s_q.id" %(self.code_metadata['template'],args['port'])
            
        # handler exit transition
        elif self.origin in edge['target']:
            edge['sync'] = "handlerexit!"
            
        elif '_activate' in edge['target']:
            edge['sync'] = "%s_%s_activate!" %(self.code_metadata['template'],args['port'])
            
        elif '_deactivate' in edge['target']:
            edge['sync'] = "%s_%s_deactivate!" %(self.code_metadata['template'],args['port'])
            
        elif '_launch' in edge['target']:
            edge['sync'] = "%s_%s_start!" %(self.code_metadata['template'],args['port'])
            
        elif '_cancel' in edge['target']:
            edge['sync'] = "%s_%s_cancel!" %(self.code_metadata['template'],args['port'])
            
        elif '_terminate' in edge['target']:
            edge['sync'] = "%s_%s_terminate!" %(self.code_metadata['template'],args['port'])
            
        elif 'setDelay' in edge['target']:
            edge['sync'] = "%s_%s_setDelay!" %(self.code_metadata['template'],args['port'])
            edge['assign'] = "%s_%s_delay = %d" %(self.code_metadata['template'],args['port'], args['attr']['period'])
            
        else:
            edge['sync'] = "go?"
            
        if 'user_op' in edge['source']:
            edge['guard'] = "exec_time >= %d" %(args['min']*10)
    
    def add_riaps_ports(self):
        sequence = {}
        for nid,node in CFGNode.cache.items():
            if node.calls:
                for calls in node.calls:
                    if calls in self.functions:
                        if 'init' not in calls:
                            # called = self.get_defining_function(node)
                            # print(node.lineno())
                            sequence[node.lineno()]=(node,calls,'func',None)
                            # self.add_ta_edges(calls, called)
                        
                    elif 'send_pyobj' in calls:
                        port_name = node.ast_node.value.func.value.attr
                        self.code_metadata['locations'].append({'id': 'post_send_%s' % node.lineno(), 'commit' : True})
                        self.code_metadata['committed'].append('post_send_%s' % node.lineno())
                        sequence[node.lineno()]=(node,'post_send_%s' % node.lineno(),'send',port_name)
                        # called = self.get_defining_function(node)
                        # rcalled = self.get_returning_function(called)
                        # # print(called+','+rcalled)
                        # idx = self.add_ta_edges(rcalled, called)
                        # if idx >= 0:
                        #     self.code_metadata['edges'][idx].setdefault('update',[]).append('intq.%s = 1' % port_name)
                                            
                    elif 'recv_pyobj' in calls:
                        port_name = node.ast_node.value.func.value.attr
                        self.code_metadata['locations'].append({'id': 'pre_recv_%s' % node.lineno(), 'commit' : True})
                        self.code_metadata['committed'].append('pre_recv_%s' % node.lineno())
                        self.code_metadata['locations'].append({'id': 'post_recv_%s' % node.lineno(), 'commit' : True})
                        self.code_metadata['committed'].append('post_recv_%s' % node.lineno())
                        self.code_metadata['locations'].append({'id': 'blocking_%s' % node.lineno()})
                        sequence[node.lineno()-0.1]=(node,'pre_recv_%s' % node.lineno(),'recv',port_name)
                        # sequence[node.lineno()]=(node,'blocking_%s' % node.lineno(),'recv',port_name)
                        self.add_ta_edges('pre_recv_%s' %(node.lineno()), 'blocking_%s' %(node.lineno()), None)
                        self.add_ta_edges('blocking_%s' % (node.lineno()), 'pre_recv_%s' % (node.lineno()), {'port' : port_name})
                        sequence[node.lineno()+0.1]=(node,'post_recv_%s' % node.lineno(),'recv',port_name)
                        # called = self.get_defining_function(node)
                        # rcalled = self.get_returning_function(called)
                        # # print(called)
                        # # print(rcalled)
                        # idx = self.add_ta_edges(called, rcalled)
                        # if idx >= 0:
                        #     self.code_metadata['edges'][idx].setdefault('update',[]).append('intq.%s = 0' % port_name)
                            # self.code_metadata['edges'][idx].setdefault('guard',[]).append('intq.%s == 1' % port_name)
                    elif 'activate' == calls:
                        port_name = node.ast_node.value.func.value.attr
                        self.code_metadata['locations'].append({'id': '%s_%s_%s' % (port_name,calls,node.lineno()), 'commit' : True})
                        self.code_metadata['committed'].append('%s_%s_%s' % (port_name,calls,node.lineno()))
                        sequence[node.lineno()]=(node,'%s_%s_%s' % (port_name,calls,node.lineno()),'tim',port_name)
                        
                    elif 'deactivate' == calls:
                        port_name = node.ast_node.value.func.value.attr
                        self.code_metadata['locations'].append({'id': '%s_%s_%s' % (port_name,calls,node.lineno()), 'commit' : True})
                        self.code_metadata['committed'].append('%s_%s_%s' % (port_name,calls,node.lineno()))
                        sequence[node.lineno()]=(node,'%s_%s_%s' % (port_name,calls,node.lineno()),'tim',port_name)
                        
                    elif 'launch' == calls:
                        port_name = node.ast_node.value.func.value.attr
                        self.code_metadata['locations'].append({'id': '%s_%s_%s' % (port_name,calls,node.lineno()), 'commit' : True})
                        self.code_metadata['committed'].append('%s_%s_%s' % (port_name,calls,node.lineno()))
                        sequence[node.lineno()]=(node,'%s_%s_%s' % (port_name,calls,node.lineno()),'tim',port_name)
                        
                    elif 'cancel' == calls:
                        port_name = node.ast_node.value.func.value.attr
                        self.code_metadata['locations'].append({'id': '%s_%s_%s' % (port_name,calls,node.lineno()), 'commit' : True})
                        self.code_metadata['committed'].append('%s_%s_%s' % (port_name,calls,node.lineno()))
                        sequence[node.lineno()]=(node,'%s_%s_%s' % (port_name,calls,node.lineno()),'tim',port_name)
                        
                    elif 'terminate' == calls:
                        port_name = node.ast_node.value.func.value.attr
                        self.code_metadata['locations'].append({'id': '%s_%s_%s' % (port_name,calls,node.lineno()), 'commit' : True})
                        self.code_metadata['committed'].append('%s_%s_%s' % (port_name,calls,node.lineno()))
                        sequence[node.lineno()]=(node,'%s_%s_%s' % (port_name,calls,node.lineno()),'tim',port_name)
                        
                        
                    elif 'setDelay' == calls:
                        port_name = node.ast_node.value.func.value.attr
                        self.code_metadata['locations'].append({'id': '%s_%s_%s' % (port_name,calls,node.lineno()), 'commit' : True})
                        self.code_metadata['committed'].append('%s_%s_%s' % (port_name,calls,node.lineno()))
                        sequence[node.lineno()]=(node,'%s_%s_%s' % (port_name,calls,node.lineno()),'tim',port_name)
                        
                        if node.ast_node.value.args[0].__class__.__name__.lower() == 'num':
                            self.port_data[self.code_metadata['template']]['ports'][port_name]['period'] = node.ast_node.value.args[0].n
                        else:
                            self.port_data[self.code_metadata['template']]['ports'][port_name]['period'] = random.randint(1, 10)
        prev = None
        next = self.origin
        curr_chain = None
        key_list=sorted(sequence.keys())
        for i,lineno in enumerate(key_list):
        #for lineno, tup in sorted(sequence.items()):
            tup = sequence[lineno]
            node, calls, type, port_nm = tup
            called = self.get_defining_function(node)
            if called.startswith('on_'):
                curr_chain = called
            #print('calls'+calls)
            if i < len(key_list) - 1:
                next_node = sequence[key_list[i+1]][0]
                #print([loc['id'].split("_")[-1] for loc in self.code_metadata["locations"]])
                usr_locs = [(i,loc) for i,loc in enumerate(self.code_metadata['locations']) if loc['id'].startswith('user_') and float(loc['id'].split("_")[-1]) < next_node.lineno() and float(loc['id'].split("_")[-1]) > node.lineno()]
            else:
                next_node = None
                for loc in self.code_metadata["locations"]: 
                    if loc["id"].startswith("on_"):
                        next_loc = loc
                        break
                usr_locs = [(i,loc) for i,loc in enumerate(self.code_metadata['locations']) if loc['id'].startswith('user_') and float(loc['id'].split("_")[-1]) < float(next_loc['id'].split("_")[-1]) and float(loc['id'].split("_")[-1]) > node.lineno()]
                
            if port_nm is not None:
                port_info = self.port_data[self.code_metadata['template']]['ports'][port_nm]
                args = {'port' : port_nm, 'attr' : port_info}
            else:
                args = None
                
            if len(usr_locs) > 0:
                for i,loc in usr_locs:
                    args = {'min': self.code_metadata['locations'][i]['min'],
                            'max': self.code_metadata['locations'][i]['max']}
                    self.add_ta_edges(loc['id'], calls, args)
                self.add_ta_edges(next, loc['id'], args)
                continue
            if (prev is None) or (called != self.get_defining_function(prev[0])):
                called = self.get_defining_function(node)
                self.add_ta_edges(calls, called, args)
                # if prev is None:
                #     next = called
                prev = tup
            else:
                self.add_ta_edges(calls, prev[1],args)
                prev = tup
            if next_node is not None:
                if self.get_defining_function(next_node).startswith('on_') and curr_chain != self.get_defining_function(next_node):
                    # print('curr chain'+curr_chain)
                    # print('new chain'+self.get_defining_function(next_node))
                    # print('calls'+calls)
                    
                    self.add_ta_edges(next,calls)
            # if len(node.children) != 0:
            #     print(calls)
            #     print(node.children)
        # print(self.code_metadata['template'])
        # print('outside'+calls)
        # print('next'+next)
        self.add_ta_edges(next,calls)
                    
                        
                        
                        
    def get_returning_function(self,called):
        rcalled = 'ready'
        for nnid,nnode in CFGNode.cache.items():
            if nnode.calls:
                for rcalls in nnode.calls:
                    # print(rcalls)
                    if called in rcalls:
                        rcalled = self.get_defining_function(nnode)
        return rcalled
        
                        

    def gen_cfg(self, src, port_data):
        """
        >>> i = PyCFG()
        >>> i.walk("100")
        5
        """
        CFGNode.cache = {}
        CFGNode.registry = 0
        self.port_data = port_data
        node = self.parse(src)
        nodes = self.walk(node, [self.founder])
        self.last_node = CFGNode(parents=nodes, ast=horast.parse('stop').body[0])
        tast.copy_location(self.last_node.ast_node, self.founder.ast_node)
        self.update_children()
        self.update_functions()
        self.link_functions()
        self.add_riaps_ports()
        
class BatchSchedulerModel:
    def __init__(self, comp_name, port_data):
        self.scheduler_metadata = {}
        #self.scheduler_metadata['local_variables']=[]
        self.scheduler_metadata['template'] = comp_name
        self.scheduler_metadata['guard'] = ''
        self.scheduler_metadata['assign']=''
        self.port_data = port_data
        
    def gen_cfg(self):
        self.scheduler_metadata['guard'] = '||'.join('%s_%s_q.curr_size > 0' %(self.scheduler_metadata['template'],port_name) for port_name in self.port_data['ports'])
        self.scheduler_metadata['assign'] = ','.join('poll(%s_%s_q)' %(self.scheduler_metadata['template'],port_name) for port_name in self.port_data['ports'])

def compute_dominator(cfg, start = 0, key='parents'):
    dominator = {}
    dominator[start] = {start}
    all_nodes = set(cfg.keys())
    rem_nodes = all_nodes - {start}
    for n in rem_nodes:
        dominator[n] = all_nodes

    c = True
    while c:
        c = False
        for n in rem_nodes:
            pred_n = cfg[n][key]
            doms = [dominator[p] for p in pred_n]
            i = set.intersection(*doms) if doms else set()
            v = {n} | i
            if dominator[n] != v:
                c = True
            dominator[n] = v
    return dominator

def slurp(f):
    with open(f, 'r') as f: return f.read()

def gen_cfg(fnsrc, remove_start_stop=True):
    CFGNode.cache = {}
    CFGNode.registry = 0
    cfg = PyCFG()
    cfg.gen_cfg(fnsrc)
    cache = dict(CFGNode.cache)
    if remove_start_stop:
        return {k:cache[k] for k in cache if cache[k].source() not in {'start', 'stop'}}
    else:
        return cache

def to_graph(cache, arcs=[]):
    def unhack(v):
        for i in ['if', 'while', 'for', 'elif']:
            v = re.sub(r'^_%s:' % i, '%s:' % i, v)
        return v
    G = pygraphviz.AGraph(directed=True)
    cov_lines = set(i for i,j in arcs)
    for nid, cnode in cache.items():
        G.add_node(cnode.rid)
        n = G.get_node(cnode.rid)
        lineno = cnode.lineno()
        n.attr['label'] = "%d: %s" % (lineno, unhack(cnode.source()))
        # print(cnode.source())
        for pn in cnode.parents:
            plineno = pn.lineno()
            if hasattr(pn, 'calllink') and pn.calllink > 0 and not hasattr(cnode, 'calleelink'):
                G.add_edge(pn.rid, cnode.rid, style='dotted', weight=100)
                continue

            if arcs:
                if  (plineno, lineno) in arcs:
                    G.add_edge(pn.rid, cnode.rid, color='green')
                elif plineno == lineno and lineno in cov_lines:
                    G.add_edge(pn.rid, cnode.rid, color='green')
                elif hasattr(cnode, 'fn_exit_node') and plineno in cov_lines:  # child is exit and parent is covered
                    G.add_edge(pn.rid, cnode.rid, color='green')
                elif hasattr(pn, 'fn_exit_node') and len(set(n.lineno() for n in pn.parents) | cov_lines) > 0: # parent is exit and one of its parents is covered.
                    G.add_edge(pn.rid, cnode.rid, color='green')
                elif plineno in cov_lines and hasattr(cnode, 'calleelink'): # child is a callee (has calleelink) and one of the parents is covered.
                    G.add_edge(pn.rid, cnode.rid, color='green')
                else:
                    G.add_edge(pn.rid, cnode.rid, color='red')
            else:
                if cnode.kind == True:
                    G.add_edge(pn.rid, cnode.rid, color='blue', label='T')
                else:
                    G.add_edge(pn.rid, cnode.rid)
    return G

def get_cfg(pythonfile):
    cfg = PyCFG()
    cfg.gen_cfg(slurp(pythonfile).strip())
    cache = CFGNode.cache
    g = {}
    for k,v in cache.items():
        j = v.to_json()
        at = j['at']
        parents_at = [cache[p].to_json()['at'] for p in j['parents']]
        children_at = [cache[c].to_json()['at'] for c in j['children']]
        if at not in g:
            g[at] = {'parents':set(), 'children':set()}
        # remove dummy nodes
        ps = set([p for p in parents_at if p != at])
        cs = set([c for c in children_at if c != at])
        g[at]['parents'] |= ps
        g[at]['children'] |= cs
        if v.calls:
            g[at]['calls'] = v.calls
        g[at]['function'] = cfg.functions_node[v.lineno()]
    return (g, cfg.founder.ast_node.lineno, cfg.last_node.ast_node.lineno)

def compute_flow(pythonfile):
    cfg,first,last = get_cfg(pythonfile)
    return cfg, compute_dominator(cfg, start=first), compute_dominator(cfg, start=last, key='children')

if __name__ == '__main__':
    import json
    import sys
    import argparse
    parser = argparse.ArgumentParser()
    parser.add_argument('pythonfile', help='The python file to be analyzed')
    parser.add_argument('-d','--dots', action='store_true', help='generate a dot file')
    parser.add_argument('-c','--cfg', action='store_true', help='print cfg')
    parser.add_argument('-x','--coverage', action='store', dest='coverage', type=str, help='branch coverage file')
    parser.add_argument('-y','--ccoverage', action='store', dest='ccoverage', type=str, help='custom coverage file')
    args = parser.parse_args()
    if args.dots:
        arcs = None
        if args.coverage:
            cdata = coverage.CoverageData()
            cdata.read_file(filename=args.coverage)
            arcs = [(abs(i),abs(j)) for i,j in cdata.arcs(cdata.measured_files()[0])]
        elif args.ccoverage:
            arcs = [(i,j) for i,j in json.loads(open(args.ccoverage).read())]
        else:
            arcs = []
        cfg = PyCFG()
        cfg.gen_cfg(slurp(args.pythonfile).strip())
        g = CFGNode.to_graph(CFGNode.cache, arcs)
        g.draw(args.pythonfile + '.png', prog='dot')
        print(g.string(), file=sys.stderr)
    elif args.cfg:
        cfg,first,last = get_cfg(args.pythonfile)
        for i in sorted(cfg.keys()):
            print(i,'parents:', cfg[i]['parents'], 'children:', cfg[i]['children'])