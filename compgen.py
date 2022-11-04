import horast

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

tree =horast.parse(s)
print(horast.dump(tree))