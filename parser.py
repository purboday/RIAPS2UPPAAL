from pythoncfg import *
import sys
import json
import argparse
import xml.etree.ElementTree as ET
import random
from tokenize import tokenize, untokenize, NUMBER, STRING, NAME, OP, COMMENT
from io import BytesIO
import re
from riaps.lang.lang import compileModel, LangError
from riaps.utils.config import Config
import sys
from textx.metamodel import metamodel_from_file
from textx.export import metamodel_export, model_export
from textx.exceptions import TextXSemanticError, TextXSyntaxError
import textx.model
import os
from jinja2 import FileSystemLoader, Environment

XMIN = -500
XMAX = 500
YMIN = -500
YMAX = 500

s = """
# riaps:keep_import:begin
from riaps.run.comp import Component
import spdlog
import capnp
import relaymonitor_capnp
import random

# riaps:keep_import:end

class RelayDevice(Component):
# ta template: RelayDevice
# ta variables : base,dev,RelayStatus,msg
#ta location : newState
# ta source:  on_delay ; target :newState
# riaps:keep_constr:begin
    def __init__(self, base, dev):
        super(RelayDevice, self).__init__()
        self.base = base
        self.dev = dev
        self.currStatus=random.randint(0, 1)
        self.period = None
# riaps:keep_constr:end

# riaps:keep_delay:begin
    def on_delay(self):
        now=self.delay.recv_pyobj()
        #ta update msg=0
        msg=(random.randint(0, 1),now)
        self.logger.info('publishing relay status')
        # ta update 
        self.SendRelayStatus.send_pyobj(msg)
        self.period = self.base + self.dev*random.random()
        self.delay.setPeriod(self.period)
        if dev < base:
            set= 2*wet
        setupTimer()
# riaps:keep_delay:end

# riaps:keep_impl:begin
    def setupTimer(self):
        print('inside setupTimer()')
        self.SendRelayStatus.send_pyobj('test')

# riaps:keep_impl:end

"""

class riaps2uppaal():
    def __init__(self, filename):
        self.filename = filename
        self.cfg = PyCFG()
        self.g = None
        self.modelData = {}
        self.env = Environment(
            loader = FileSystemLoader("templates"))
        
    def generate_cfg(self):
        self.cfg.gen_cfg(s, self.modelData)
        self.g = to_graph(CFGNode.cache, [])
        
    def print_cfg(self):
        if self.g is not None:
            return self.g.to_string()
            
    def generate_xml(self, start_new = True):
        
        if start_new:
            root=ET.Element('nta')
            comment=ET.Comment("DOCTYPE nta PUBLIC '-//Uppaal Team//DTD Flat System 1.1//EN' 'http://www.it.uu.se/research/group/darts/uppaal/flat-1_2.dtd'")
            root.append(comment)
            decl = ET.SubElement(root, 'declaration')
            decl_text = ''
            for varb in self.cfg.code_metadata['global_variables']:
                decl_text += 'int %s;' % (varb)
            decl.text = decl_text
            templ = ET.SubElement(root,'template')
            
        else:
            templ=ET.Element('template')
        
        
        xlist = list(range(XMIN,XMAX))
        random.shuffle(xlist)
        ylist = list(range(XMIN,XMAX))
        random.shuffle(ylist)
        i =0
        j=0
        templ_name = ET.SubElement(templ,'name', {'x': str(xlist[i]), 'y': str(ylist[j])})
        i+=1
        j+=1
        templ_name.text = self.cfg.code_metadata['template']
        paramt = ET.SubElement(templ,'parameters')
        paramt_text = ''
        for arg in self.cfg.code_metadata['arguments']:
            paramt_text += 'int %s,' % arg
        paramt_text = paramt_text[0:-1]
        paramt.text = paramt_text
        loc_decl = ET.SubElement(templ,'declaration')
        loc_decl_text = ''
        for varb in self.cfg.code_metadata['local_variables']:
            loc_decl_text += 'int %s;' % (varb)
        loc_decl.text = loc_decl_text
        loc_xy = {}
        for locs in self.cfg.code_metadata['locations']:
            locn = ET.SubElement(templ,'location',{'id': locs['id'], 'x': str(xlist[i]), 'y': str(ylist[j])})
            locn_name = ET.SubElement(locn,'name',{'x': str(xlist[i]+5), 'y': str(ylist[j]+10)})
            locn_name.text = locs['id']
            loc_xy[locs['id']]=(xlist[i],ylist[j])
            if 'invariant' in locs:
                invt = ET.SubElement(locn,'label', {'kind': 'invariant', 'x': str(xlist[i]), 'y': str(ylist[j]+20)})
                invt.text = locs['invariant']
            if 'init' in locs:
                ET.SubElement(templ,'init',{'ref' : locs['id']})
            i+=1
            j+=1
        for edge in self.cfg.code_metadata['edges']:
            transition = ET.SubElement(templ,'transition')
            src = ET.SubElement(transition,'source',{'ref':edge['source']})
            target = ET.SubElement(transition,'target',{'ref':edge['target']}) 
            if 'guard' in edge:
                guard = ET.SubElement(locn,'label', 
                                      {'kind': 'guard', 'x': str(int((loc_xy[edge['source']][0]+loc_xy[edge['target']][0])/2)), 
                                       'y': str(int((loc_xy[edge['source']][1]+loc_xy[edge['target']][1])/2 + 10))})
                guard.text = '&'.join(edge['guard'])
            if 'update' in edge:
                upd = ET.SubElement(locn,'label', 
                                      {'kind': 'assignment', 'x': str(int((loc_xy[edge['source']][0]+loc_xy[edge['target']][0])/2)), 
                                       'y': str(int((loc_xy[edge['source']][1]+loc_xy[edge['target']][1])/2 - 10))})
                upd.text = ','.join(edge['update'])
            
        if start_new:
            print(ET.tostring(root, 'utf-8'))
        else:
            print(ET.tostring(templ, 'utf-8'))
        
    # def parse_comments(self):
    #     result = []
    #     g = tokenize(BytesIO(s.encode('utf-8')).readline)
    #     for toknum, tokval, _, _, _ in g:
    #         if toknum == COMMENT:
    #             # pat=re.compile(r'(?:#\s*ta\s*)(.+\s*;?\s*)+')
    #             pat = re.compile(r'(?:#\s*ta\s*)(.+)(?:\s*:\s*)(.+\s*,?\s*)+') # (.+)(?:\s*:\s*)(.+\s*,?\s*)+
    #             m=pat.match(untokenize([(toknum,tokval)]))
    #             if m:
    #                 print(m.groups())
    #             print(untokenize([(toknum,tokval)]))
    
    def parse_model(self):
        thisFolder = '/home/riaps/workspace/RIAPS2UPPAAL'
        compiledApp = compileModel('/home/riaps/workspace/RelayMonitor/RelayMonitor.riaps')
        self.appName = list(compiledApp.keys())[0]
        with open(self.appName+'.json') as f:
            data = json.load(f)
            for comp, compObj in data['components'].items():
                self.modelData[compObj['name']]={'ports' : {}}
                for portType, portObjs in compObj['ports'].items():
                    for portName, portAttr in portObjs.items():
                        insert = {'type' : portType[:-1]}
                        if portType in ['pubs','subs']:
                            insert['msgtype']= [portAttr['type']]
                        if portType in ['reqs','reps','qrys','anss','clts','srvs']:
                            insert['msgtype'] = [portAttr['reqtype'],portAttr['reptype']]
                        if portType in ['tims']:
                            insert['period'] = portAttr['period']
                            if portAttr['period'] == 0:
                                insert['timertype'] = 'sporadic'
                            else:
                                insert['timertype'] = 'periodic'
                        #self.ports.append({portName: insert})
                        self.modelData[compObj['name']]['ports'][portName]=insert
                        
    def add_xta(self, template, args):
        template = self.env.get_template(template)
        print(template.render(args))
            
    def merge_xta(self):
        #self.add_xta("genericComponent.jinja", {'compInfo' : self.cfg.code_metadata})
        for compName, ports in self.modelData.items():
            if compName == self.cfg.code_metadata["template"]:
                self.add_xta("genericComponent.jinja", {'compInfo' : self.cfg.code_metadata})
            for portName, portAttr in ports["ports"].items():
                if portAttr["type"] == "tim":
                    self.add_xta("timer.jinja", {"comp_name": compName, "port_name" : portName, "port" : portAttr})
        
obj = riaps2uppaal('rrr')
obj.parse_model()
obj.generate_cfg()
# print(obj.cfg.code_metadata)
obj.merge_xta()
# g = obj.print_cfg()
#print(g)
# obj.generate_xml()
# obj.parse_comments()