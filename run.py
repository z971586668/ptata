import check
import os
import json
import time
from pta.pta import *



files = os.listdir('./')
pta = check.read_from_json(sys.argv[1])
pta.validate()
start_time = time.time()

l_events = {"l"}
h_events = {eve for eve in pta.events if eve != 'l'}
print(h_events)

print("checking non-iterference")
inter_time = time.time()
ppl = pta.project(l_events)
phh = pta.hide(h_events)
delta = []
# for cloc in pta.clocks:
#     delta.append(cloc + ' >= 0')
delta.append('_d0_ >= 0')
pzg = PZG(ppl.events, [], (ppl.init_loc, [phh.init_loc], delta, delta, 0), [], [])
check.lang_inclusive_check(pzg, ppl, phh, inter_time)
print('time for inter : ', time.time() - inter_time)

print("checking non-deducibility")
dedu_time = time.time()
ppl = pta.project(l_events)
pph = pta.project(h_events)
parallel_ppl_pph = ppl.parallel(pph)
delta = []
delta.append('_d0_ >= 0')
pzg = PZG(parallel_ppl_pph.events, [],(parallel_ppl_pph.init_loc, [pta.init_loc], delta, delta, 0),[], [])
check.lang_inclusive_check(pzg, parallel_ppl_pph, pta, dedu_time)
print('time for deduci : ', time.time() - dedu_time)


print('complete time : ', time.time() - start_time)