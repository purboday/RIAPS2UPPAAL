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

def split_dirname(path):
    assert os.path.isdir(path), "could not find the application directory"
    head, tail = os.path.split(path)
    if not tail:
        tail = os.path.basename(head)
    return (head,tail)

class riaps2uppaal():
    def __init__(self, appFolder, appName):
        #self.appFolder, self.appName = split_dirname(appPath)
        self.appFolder =  appFolder
        self.appName = appName
        self.cfg = {}
        self.g = []
        self.modelData = {}
        self.env = Environment(
            loader = FileSystemLoader("templates"))
        self.sched = {}
        self.xtaFile = "%s/%s.xta" %(self.appFolder,self.appName)
        self.xtaContent = []
        
    def generate_cfg(self):
        assert self.modelData, "call parse_model() first to get model data"
        for compName in self.modelData:
            fileName = "%s/%s.py" %(self.appFolder,compName)
            if os.path.isfile(fileName):
                with open(fileName,'r') as file:
                    compCode = file.read()
                    self.cfg[compName]=PyCFG()
                    self.cfg[compName].gen_cfg(compCode, self.modelData)
                    self.g.append(to_graph(CFGNode.cache, []))
                    # compName = self.cfg[-1].code_metadata['template']
                    self.sched[compName]=BatchSchedulerModel(compName, self.modelData[compName])
                    self.sched[compName].gen_cfg()
            else:
                print("file %s.py not found in %s" %(compName, self.appFolder))
        
    def print_cfg(self):
        graphs = []
        if self.g is not None:
            for item in self.g:
                graphs.append(item.to_string())
        return graphs
            
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
    
    def parse_model(self, modelFile=None):
        #thisFolder = '/home/riaps/workspace/RIAPS2UPPAAL'
        if not modelFile:
            modelFile = "%s.riaps" % (self.appName)
        try:
            compiledApp = compileModel('%s/%s' %(self.appFolder,modelFile))
        except:
            raise
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
                            insert['msgtype'] = [portAttr['req_type'],portAttr['rep_type']]
                        if portType in ['tims']:
                            insert['period'] = portAttr['period']
                            if portAttr['period'] == 0:
                                insert['timertype'] = 'sporadic'
                            else:
                                insert['timertype'] = 'periodic'
                        #self.ports.append({portName: insert})
                        self.modelData[compObj['name']]['ports'][portName]=insert
                        
    def add_xta(self, template, args={}):
        if template.split('.')[0] not in self.xtaContent:
            if template.split('.')[0] not in ["genericComponent","batchScheduler"]:
                self.xtaContent.append(template.split('.')[0])
            template = self.env.get_template(template)
            with open(self.xtaFile,'a')  as file:
                file.write(template.render(args)+"\n")
            #print(template.render(args))
            
    def calc_port_count(self):
        return max(len(compData['ports']) for compName, compData in self.modelData.items())
            
    def merge_xta(self):
        
        self.add_xta("globalDecl.jinja", {'compInfo' : self.modelData, 'maxSize': 10, 'portCount' : self.calc_port_count()})
        for compName, ports in self.modelData.items():
            if compName in self.cfg:
                self.add_xta("genericComponent.jinja", {'compInfo' : self.cfg[compName].code_metadata})
                self.add_xta("batchScheduler.jinja", {'compInfo' : self.sched[compName].scheduler_metadata})
            for portName, portAttr in ports["ports"].items():
                if portAttr["type"] == "tim":
                    self.add_xta("timer.jinja", {"comp_name": compName, "port_name" : portName, "port" : portAttr})
                    #self.xtaContent.append("timer")
                if portAttr["type"] == "sub":
                    self.add_xta("subscribe.jinja")
                    #nd("timer")
                if portAttr["type"] == "req":
                    self.add_xta("request.jinja")
                if portAttr["type"] == "rep":
                    self.add_xta("reply.jinja")
                    #self.xtaContent.append("reply")
                if portAttr["type"] == "qry":
                    self.add_xta("query.jinja")
                    #self.xtaContent.append("query")
                if portAttr["type"] == "ans":
                    self.add_xta("answer.jinja")
                    #self.xtaContent.append("answer")
        self.add_xta("urgentEdge.jinja")
        self.add_xta("templateInst.jinja", {'compInfo' : self.modelData})
        
obj = riaps2uppaal('/home/riaps/riaps_projects/DistributedEstimator/Python/','DistributedEstimator')
obj.parse_model('sample.riaps')
obj.generate_cfg()
# for comp, item in obj.cfg.items():
#     print(item.code_metadata)
obj.merge_xta()
# g = obj.print_cfg()
# for item in g:
#     print(item)
# obj.generate_xml()
# obj.parse_comments()