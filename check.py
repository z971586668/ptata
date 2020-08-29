from z3 import *
from pta.pta import *
import json
import time
from sympy import *

LOCATIONS = 'locations'
EVENTS = 'events'
INIT_LOC = 'init_loc'
CLOCKS = 'clocks'
PARAMETERS = 'parameters'
INVARIANTS = 'invariants'
EDGES = 'edges'
PARAM_INV = 'param_inv'
INIT_CLOCK = 'z0_'
INIT_DELAY = '_d0_'
CLOCK = 'z'
DELAY = '_d'
TAO = 'tao'

def read_from_json(json_file_path) :
    json_file = open(json_file_path, 'r')
    json_obj = json.loads(json_file.read())
    locations = json_obj[LOCATIONS]
    events = json_obj[EVENTS]
    init_loc = json_obj[INIT_LOC]
    clocks = json_obj[CLOCKS]
    parameters = json_obj[PARAMETERS]
    invariants = json_obj[INVARIANTS]
    edges = json_obj[EDGES]
    param_inv = json_obj[PARAM_INV]
    pta = PTA(events, locations, init_loc, clocks, parameters, invariants, edges, param_inv)
    return pta

def add_z3_variable(pa, sa) :
    keys = []
    for p in pa.parameters :
        keys.append(p)
    for p in sa.parameters :
        keys.append(p)
    for cloc in pa.clocks :
        keys.append(cloc)
    for cloc in sa.clocks :
        keys.append(cloc)
    var_dict = {}
    for k in keys :
        var_dict[k] = z3.Int(k)
    var_dict[INIT_CLOCK] = z3.Int(INIT_CLOCK)
    var_dict[INIT_DELAY] = z3.Int(INIT_DELAY)
    return var_dict
    
def add_symbol_variable(pa, sa) :
    keys = []
    for p in pa.parameters :
        keys.append(p)
    for p in sa.parameters :
        keys.append(p)
    for cloc in pa.clocks :
        keys.append(cloc)
    for cloc in sa.clocks :
        keys.append(cloc)
    var_dict = {}
    reverse_dict = {}
    for k in keys :
        var_dict[k] = symbols(k)
        reverse_dict[symbols(k)] = k
    var_dict[INIT_DELAY] = symbols(INIT_DELAY)
    var_dict[INIT_CLOCK] = symbols(INIT_CLOCK)
    reverse_dict[symbols(INIT_DELAY)] = INIT_DELAY
    return var_dict, reverse_dict

def get_edges_pa(pa, current) : 
    pa_edges = [e for e in pa.edges if e['from'] == current[0] ]
    return pa_edges
    
def get_edges_sa(ps, current, ep) :
    sa_edges = [e for e in ps.edges if e['from'] in current[1] and e['event'] == ep['event']]
    return sa_edges

def add_transition(current, ep, es, unfold_tran, pa, transition, working, working_set, sym_) :
    s_from = (current[0], tuple(current[1]), tuple(current[2]), current[3], current[4])
    delta = set()
    for c in current[2] :
            delta.add(c)
    for c in ep['guard'] :
            delta.add(c)
    for cloc in ep['clock'] : 
        delta.add(cloc + ' == 0' )
    if es == '' and unfold_tran == '' :
        if ep['event'] != TAO :
            s_to = (ep['to'], tuple([]), tuple(list(delta)), tuple(list(delta)), current[4] + 1)
            obj = {'from' : s_from, 'to' : s_to, 'event' : ep['event']}
            return obj
        elif ep['event'] == TAO :
            delta.add(DELAY + str(current[4]) + '_' + ' >= 0')
            delay_delta = set()
            history_delta = set()
            for c in delta :
                if '==' not in c and c[0:1] != '_d' and c[1:2] != '_d' and c[2:3] != '_d':
                    history_delta.add(c)
                for cloc in pa.clocks :
                    c = c.replace(cloc, cloc + ' - ' + DELAY + str(current[4]) + '_')
                c = c.replace(CLOCK + '0_', CLOCK + '0_' + ' - ' + DELAY + str(current[4]) + '_')
                delay_delta.add(c)
            s_to = (ep['to'], tuple(current[1]), tuple(list(delay_delta)), tuple(list(history_delta)), current[4] + 1)
    elif es == '' and unfold_tran != '' and ep['event'] == TAO :
        delta.add(CLOCK + str(unfold_tran['from'][2]) + '_ == 0')
        delta.add(DELAY + str(current[4]) + '_' + ' >= 0')
        delay_delta = set()
        history_delta = set()
        for c in delta :
            if '==' not in c and c[0:1] != '_d' and c[1:2] != '_d' and c[2:3] != '_d':
                history_delta.add(c)
            for cloc in pa.clocks :
                c = c.replace(cloc, cloc + ' - ' + DELAY + str(current[4]) + '_')
            tmp = ' '
            for k in c.split() :
                if k[0] == 'z' :
                    if int(k[1:-1]) in unfold_tran['from'][1].values() : 
                        tmp += k + ' - ' + DELAY + str(current[4]) + '_' + ' '
                    else : 
                        tmp += k + ' '
                else :
                    tmp += k + ' '
            c = tmp
            delay_delta.add(c)
        s_to = (ep['to'], tuple(current[1]), tuple(list(delay_delta)), tuple(list(history_delta)), current[4] + 1)
    if es != '' and unfold_tran != '' and ep['event'] != TAO :
        delta.add(CLOCK + str(unfold_tran['from'][2]) + '_ == 0')
        delta.add(DELAY + str(current[4]) + '_' + ' >= 0')
        for cloc in ep['clock'] : 
            delta.add(cloc + ' == 0' )
        for c in unfold_tran['guard'] : 
            delta.add(c)
        delay_delta = set()
        history_delta = set()
        for c in delta :
            if '==' not in c and c[0:1] != '_d' and c[1:2] != '_d' and c[2:3] != '_d':
                delay_delta.add(c)
            for cloc in pa.clocks :
                c = c.replace(cloc, cloc + ' - ' + DELAY + str(current[4]) + '_')
            tmp = ' '
            for k in c.split() :
                if k[0] == 'z' :
                    if int(k[1:-1]) in unfold_tran['from'][1].values() : 
                        tmp += k + ' - ' + DELAY + str(current[4]) + '_' + ' '
                    else : 
                        tmp += k + ' '
                else :
                    tmp += k + ' '
            c = tmp
            delay_delta.add(c)
        s_to = (ep['to'], tuple([es['to']]), tuple(delay_delta), tuple(history_delta), current[4] + 1)
    obj = {'from' : s_from, 'to' : s_to, 'event' : ep['event']}
    transition.append(obj)
    if (s_to[0], tuple(s_to[1])) not in working_set :
        working_set.add((s_to[0], tuple(s_to[1])))
        working.append(s_to)
    return obj

def eliminate_delay(cons, delay_cnt, unfold_tran, sym_) :
    if unfold_tran != '':
        clock_min = delay_cnt
        for v in unfold_tran['from'][1].values():
            if v <= clock_min :
                clock_min = v
    cons_symbol = set()
    cons_copy = cons.copy()
    for c in cons_copy :
        if CLOCK + str(clock_min) + '_' in c:   
            cons.remove(c)
            continue
        for k in sym_.keys() :
            c = c.replace(k, "sym_['" + k + "']")
        c = c.replace(' == 0', ' ')
        cons_symbol.add(eval(c))
    solve(cons_symbol, sym_['_d0_'])
    
    equal_formulas = set()
    for c in cons :
        if ' == ' in c :
            equal_formulas.add(c)

def get_cons(unfold_trans, sa) :
    if len(unfold_trans) == 0:
        return []
    cons = set()
    for ut in unfold_trans:
        neg_guard = 'z3.Or( False, False, '
        for c in ut['guard']:
            if DELAY in c :
                continue
            if c in sa.param_inv :
                continue
            if '>=' in c :
                neg_guard += c.replace('>=', '<') + ', '
            elif '<=' in c :
                neg_guard += c.replace('<=', '>') + ', '
            elif '>' in c :
                neg_guard += c.replace('>', '<=') + ', '
            elif '<' in c :
                neg_guard += c.replace('<', '>=') + ', '
            elif '==' in c :
                for cloc in sa.clocks :
                    if cloc + ' == ' + CLOCK not in c :
                        neg_guard += c.replace('==', '!=') + ', '           
            elif '!=' in c :
                neg_guard += c.replace('!=', '==') + ', '
        neg_guard = neg_guard[:-2]
        neg_guard += ')'
        cons.add(neg_guard)
    return cons

def check_trans(con, delta, gp, gs, solve_):
    s = z3.Solver()  
    cons = set()
    if 'True' not in con:
        for c in con:
            cons.add(c)
    elif 'True' in con:
        cons.add(con)
    for c in delta :
        cons.add(c)
    for c in gp :
        cons.add(c)
    for c in gs :
        cons.add(c)
    for c in cons :
        for k in solve_.keys() :
            c = c.replace(k, "solve_['" + k + "']")
        s.add(eval(c))

    return s.check() == sat  


def add_inequals(c, pa, gfs, lfs, gfseq, lfseq, sym_, new_clock) :
    if '>=' in c :
        pos = c.find('>=')
        lc = c[:pos]
        rc = c[pos+2:]
        if CLOCK in lc :
            gfs.append(eval(lc) - eval(rc))
            gfseq.append(eval(lc) - eval(rc))
        elif CLOCK in rc :
            lfs.append(eval(lc) - eval(rc))
            lfseq.append(eval(lc) - eval(rc))
    elif '<=' in c :
        pos = c.find('<=')
        lc = c[:pos]
        rc = c[pos+2:]
        if CLOCK in lc :
            lfs.append(eval(lc) - eval(rc))
            lfseq.append(eval(lc) - eval(rc))
        elif CLOCK in rc :
            gfs.append(eval(lc) - eval(rc))
            gfseq.append(eval(lc) - eval(rc))
    elif '>=' not in c and '>' in c :
        pos = c.find('>')
        lc = c[:pos]
        rc = c[pos+1:]
        if CLOCK in lc : 
            gfs.append(eval(lc) - eval(rc))
        elif CLOCK in rc :
            lfs.append(eval(lc) - eval(rc))
    elif '<=' not in c and '<' in c :
        pos = c.find('<')
        lc = c[:pos]
        rc = c[pos+1:]
        if CLOCK in lc : 
            lfs.append(eval(lc) - eval(rc))
        elif CLOCK in rc :
            gfs.append(eval(lc) - eval(rc))

def solve_inequal(lfs, gfs, lfseq, gfseq, lcs_dict, gcs_dict, lcseq_dict, gcseq_dict, sym_, pa, unfold_tran, final_cons) :
    for f in gfs :
        for cloc in pa.clocks :  
            if unfold_tran != '' :
                model = solve(f, sym_[CLOCK + str(unfold_tran['from'][1][cloc]) + '_'])
            else : 
                model = solve(f, sym_[cloc])
            for m in model :
                gcs_dict[cloc].add(str(m))
    for f in lfs :
        for cloc in pa.clocks :
            if unfold_tran != '' :
                model = solve(f, sym_[CLOCK + str(unfold_tran['from'][1][cloc]) + "_"])
            else : 
                model = solve(f, sym_[cloc])
            for m in model : 
                lcs_dict[cloc].add(str(m))
    for f in gfseq :
        for cloc in pa.clocks :
            if unfold_tran != '' :
                model = solve(f, sym_[CLOCK + str(unfold_tran['from'][1][cloc]) + '_'])
            else : 
                model = solve(f, sym_[cloc])
            for m in model :
                gcseq_dict[cloc].add(str(m))
    for f in lfseq :
        for cloc in pa.clocks :
            if unfold_tran != '' :
                model = solve(f, sym_[CLOCK + str(unfold_tran['from'][1][cloc]) + '_'])
            else : 
                model = solve(f, sym_[cloc])
            for m in model : 
                lcseq_dict[cloc].add(str(m))
    
def clock_elimination(lcs_dict, gcs_dict, lcseq_dict, gcseq_dict, final_cons, pa, delay_cnt) :
    # eliminate clocks without delay
    for k in gcs_dict.keys() : 
        if len(gcs_dict[k]) == 0 or len(lcs_dict[k]) == 0:
            continue
        for g in gcs_dict[k] : 
            for l in lcs_dict[k] :
                if g in gcseq_dict[k] and l in lcseq_dict[k]:
                    continue
                final_cons.add(str(g) + ' >= ' + str(l))
    for k in gcseq_dict.keys() : 
        if len(gcs_dict[k]) == 0 or len(lcs_dict[k]) == 0:
            continue
        for g in gcseq_dict[k] : 
            for l in lcseq_dict[k] :
                final_cons.add(str(g) + ' > ' + str(l))



def delay_elimination(final_cons, delay_cnt, unfold_tran, sym_):
    min_clock = delay_cnt
    if unfold_tran != '' :
        for v in unfold_tran['from'][1].values():
            if v <= min_clock:
                v = min_clock
    if unfold_tran == '':
        min_clock = 0
    final_cons_symbol = set()
    final_cons_copy = final_cons.copy()
    for c in final_cons_copy : 
        for i in range(0, min_clock):
            if CLOCK  + str(i) + '_' in str(c) :
                final_cons.remove(c)
    for i in range(0, delay_cnt + 1) :
        final_cons.add(eval("sym_['" + DELAY + str(i) + '_' + "']" + '>= 0'))
    gcs_delay_dict = {}
    lcs_delay_dict = {}
    gcseq_delay_dict = {}
    lcseq_delay_dict = {}
    for i in range(0, delay_cnt + 1) : 
        gcs_delay_dict[i] = set()
        gcseq_delay_dict[i] = set()
        lcs_delay_dict[i] = set()
        lcseq_delay_dict[i] = set()
    no_delay_cons = set()
    for i in range(0, delay_cnt + 1) :
        for c in final_cons:
            if DELAY + str(i) + '_ >= 0' in str(c):
                continue
            if DELAY + str(i) + '_' in str(c):
                model = str(solve(c, sym_[DELAY + str(i) + '_']))
                for m in str(model).split('&'):
                    if '(' in m and ')' in m:
                        m = m.strip()[1:-1]
                    if 'oo' in m:
                        continue
                    if m[0:2] == DELAY:
                        if '>=' in m:
                            gcs_delay_dict[i].add(m.split('>=')[1])
                            gcseq_delay_dict[i].add(m.split('>=')[1])
                        elif '<=' in m:
                            lcs_delay_dict[i].add(m.split('<=')[1])
                            lcseq_delay_dict[i].add(m.split('<=')[1])
                        elif '>' in m:
                            gcs_delay_dict[i].add(m.split('>')[1])
                        elif '<' in m:
                            lcs_delay_dict[i].add(m.split('<')[1])
                    else :
                        if '>=' in m:
                            lcs_delay_dict[i].add(m.split('>=')[0])
                            lcseq_delay_dict[i].add(m.split('>=')[0])
                        elif '<=' in m:
                            gcs_delay_dict[i].add(m.split('<=')[0])
                            gcseq_delay_dict[i].add(m.split('<=')[0])
                        elif '>' in m:
                            lcs_delay_dict[i].add(m.split('>')[0])
                        elif '<' in m:
                            gcs_delay_dict[i].add(m.split('<')[0])
            if DELAY not in str(c) :
                no_delay_cons.add(str(c))
    remove_delay = set()
    for i in range(0, delay_cnt + 1) : 
        if len(lcs_delay_dict[i]) == 0 or len(gcs_delay_dict[i]) == 0:
            remove_delay.add(i)
            continue
        for l in lcs_delay_dict[i]:
             for g in gcs_delay_dict[i]:
                 if len(l) > 0 and len(g) > 0:
                    if l in lcseq_delay_dict[i] and g in gcseq_delay_dict[i]:
                        no_delay_cons.add(g + ' <= ' + l)
                    else:
                        no_delay_cons.add(g + ' < ' + l)
    final_cons = set()
    for c in no_delay_cons:
        removed = False
        for i in remove_delay:
            if DELAY + str(i) + '_' in str(c):
                removed = True
                break
        if not removed:
            for k in sym_.keys():
                c = c.replace(k, "sym_['" + k + "']")
            c = simplify_inequlas(c)
            c = eval(c)
            if str(c) != 'True':
                final_cons.add(c)
            for i in range(0, delay_cnt + 1):
                if '<' in str(c) and ' ' + DELAY + str(i) + '_' in str(c):
                    if c in final_cons:
                        final_cons.remove(c)
                    break
                if '>' in str(c) and '-' + DELAY + str(i) + '_' in str(c):
                    if c in final_cons:
                        final_cons.remove(c)
                    c = str(c).replace('-' + DELAY + str(i) + '-', ' ' )
                    for k in sym_.keys():
                        c = c.replace(k, "sym_['" + k + "']")
                    c = simplify_inequlas(c)
                    c = eval(c)
                    if str(c) != 'True':
                        final_cons.add(c)
    return final_cons



def check_valid_final_cons(final_cons, solve_, pa) : 
    s = z3.Solver() 
    for inv in pa.param_inv :
        for k in solve_.keys() :
            inv = inv.replace(k, "solve_['" + k + "']")
        s.add(eval(inv))
    final_cons_copy = final_cons.copy()
    for c in final_cons_copy :
        # if '< =' in c:
        #     continue
        z3c = str(c)
        for k in solve_.keys() :
            z3c = z3c.replace(k, "solve_['" + k + "']")
        s.push()
        s.add(eval(z3c))
        if s.check() == unsat : 
            final_cons.remove(c)
        s.pop()
        
def simplify_inequlas(f) :
    s = f
    if '>=' in f :
        s = f[:f.find('>=')] + ' - (' + f[f.find('>=')+2:] + ') >= 0'
    elif '<=' in f :
        s = f[:f.find('<=')] + ' - (' + f[f.find('<=')+2:] + ') <= 0'
    elif '> ' in f :
        s = f[:f.find('>')] + ' - (' + f[f.find('>')+1:] + ') > 0'
    elif '< ' in f :
        s = f[:f.find('<')] + ' - (' + f[f.find('<')+1:] + ') < 0'
    elif '==' in f:
        s = f[:f.find('==')] + ' - (' + f[f.find('==')+2:] + ') == 0'
    return s
  

def compute_parameter_constraints(neg_c, delta, history_delta, gp, act, unfold_tran, sym_, rsym_, pa, sa, solve_, delay_cnt) :
    cons = set()
    print("c : ", neg_c, "delta : ", delta, "gp : ", gp, "act : ", act)
    if neg_c != '' :
        cons.add(neg_c)
    for c in delta :
        cons.add(c)
    for c in gp :
        cons.add(c)
    gfs = []
    gfseq = []
    lfs = []
    lfseq = []
    final_cons = set()
    # for guards in g, gp and gs without delay
    for c in cons : 
        # change clocks with z form
        if unfold_tran != '' :
            for cloc in pa.clocks :
                new_cloc = CLOCK + str(unfold_tran['from'][1][cloc]) + '_'
                c = c.replace(cloc, new_cloc)
        # change symbols to sympy input form
        for k in sym_.keys() :
            c = c.replace(k, "sym_['" + k + "']")
        add_inequals(c, pa, gfs, lfs, gfseq, lfseq, sym_, new_cloc)
    gcs_dict = {}
    lcs_dict = {}
    gcseq_dict = {}
    lcseq_dict = {} 
    for cloc in pa.clocks :
        gcs_dict[cloc] = set()
        lcs_dict[cloc] = set()
        gcseq_dict[cloc] = set()
        lcseq_dict[cloc] = set()
    solve_inequal(lfs, gfs, lfseq, gfseq, lcs_dict, gcs_dict, lcseq_dict, gcseq_dict, sym_, pa, unfold_tran, final_cons)  
    clock_elimination(lcs_dict, gcs_dict, lcseq_dict, gcseq_dict, final_cons, pa, delay_cnt)
    final_cons_sim = set()
    for c in final_cons:
        for k in sym_.keys():
            c = c.replace(k, "sym_['" + k + "']")
        c = simplify_inequlas(c)
        if str(eval(c)) != 'True':
            final_cons_sim.add(eval(c))
    final_cons = final_cons_sim
    has_delay = True
    while has_delay and len(final_cons) != 0:
        final_cons = delay_elimination(final_cons, delay_cnt, unfold_tran, sym_)
        for c in final_cons:
            if DELAY in str(c):
                has_delay = True
                break
            else:
                has_delay = False
    check_valid_final_cons(final_cons, solve_, pa)
    if len(final_cons) == 0:
        if neg_c != '' :
            final_cons.add('False')
    check_valid_final_cons(final_cons, solve_, pa)
    print('final cons : ', final_cons, '\n')
    return final_cons

def unfolds(current, es, sa, unfolding_sa, solve_, sym_, reverse_dict) :
    # introduced a new level, new_level = level + 1
    # change clocks in guard with the mapped clock in map_clock dict
    from_loc = ''
    acts = set()
    cons = set()
    for loc in unfolding_sa.locations :
        if loc[0] == es['from'] :
            from_loc = loc
    map_clock = from_loc[1].copy()
    # change constraints based with the level clock of from location
    for c in es['guard'] : 
        for cloc in sa.clocks :
            c = c.replace(cloc, CLOCK + str(map_clock[cloc]) + '_')
        cons.add(c)
    for cloc in es['clock'] : 
        map_clock[cloc] = from_loc[2] + 1
    new_loc = (es['to'], map_clock, from_loc[2] + 1)
    solve_[CLOCK + str(from_loc[2] + 1) + '_'] = Int(CLOCK + str(from_loc[2] + 1) + '_') 
    sym_[CLOCK + str(from_loc[2] + 1) + '_'] = symbols(CLOCK + str(from_loc[2] + 1) + '_')
    reverse_dict[symbols(DELAY + str(from_loc[2] + 1)+ '_')] = DELAY + str(from_loc[2] + 1) + '_'
    unfolding_locations_set = set()
    for l in unfolding_sa.locations :
        unfolding_locations_set.add((l[0], l[2]))
    if (new_loc[0], new_loc[2]) not in unfolding_locations_set : 
        unfolding_sa.locations.append(new_loc)
        unfolding_sa.edges.append({"from" : from_loc, "to" : new_loc, "guard" : list(cons), "event" : es['event']})
    return {"from" : from_loc, "to" : new_loc, "guard" : list(cons), "event" : es['event']}
    


def lang_inclusive_check(pzg, pa, sa, start_time) :
    working = []
    working_set = set()
    working.append(pzg.init_state)
    working_set.add((pzg.init_state[0], tuple(pzg.init_state[1])))
    done = []
    transitions = []
    parameter_cons = set()
    solve_ = add_z3_variable(pa, sa)
    sym_, rsym_ = add_symbol_variable(pa, sa)
    map_clock = {}
    states_cnt = 0
    transitions_cnt = 0
    for cloc in sa.clocks :
        map_clock[cloc] = 0
    unfolding_sa = UNFOLDS([(sa.init_loc, map_clock, 0)], (sa.init_loc, 0, map_clock), [INIT_CLOCK], [])
    parameter_constraints = set()
    unfold_tran = ''
    algo_ter = False
    sa_unfolds = {}
    while(len(working) > 0) :
        current = working[0]
        solve_[DELAY + str(current[4]) + '_'] = Int(DELAY + str(current[4]) + '_')
        sym_[DELAY + str(current[4]) + '_'] = symbols(DELAY + str(current[4]) + '_')
        # print("current : ", current)
        working.remove(current)
        done.append(current)
        if len(current[1]) == 0 :
            continue
        pa_edges = get_edges_pa(pa, current)
        for ep in pa_edges :
            sa_edges = get_edges_sa(sa, current, ep)
            if len(sa_edges) == 0 :
                if ep['event'] == TAO : 
                    pzg_tran = add_transition(current, ep, '', unfold_tran, pa, transitions, working, working_set, sym_)
                    states_cnt = states_cnt + 1
                    transitions_cnt = transitions_cnt + 1
                elif ep['event'] != TAO :
                    if check_trans('True', current[2], ep['guard'], [], solve_) :
                        for k in sa_unfolds.keys() :
                            if " 'to': '" + str(current[1][0]) + "'" in k:
                                act = set()
                                act.add(cloc + ' == ' + CLOCK + str(sa_unfolds[k]['to'][1][cloc]) + '_')
                        pzg_tran = add_transition(current, ep, '', '', pa, transitions, working, working_set, sym_)
                        transitions_cnt = transitions_cnt + 1
                        print("empty tran : ", pzg_tran['from'][0], pzg_tran['from'][1], pzg_tran['to'][0], pzg_tran['to'][1])
                        param_con = compute_parameter_constraints('', current[2], current[3], ep['guard'], act, unfold_tran, sym_, rsym_, pa, sa, solve_, current[4])
                        parameter_constraints.update(param_con)
            else :
                unfold_trans = {}
                for es in sa_edges :
                    unfold_tran = unfolds(current, es, sa, unfolding_sa, solve_, sym_, rsym_)
                    unfold_trans[str(es)] = unfold_tran
                    sa_unfolds[str(es)] = unfold_tran
                # g/\gs/\gp, where gsi is the negative form in g
                unfold_trans_neg = []
                for es in sa_edges:
                    unfold_tran = unfold_trans[str(es)]
                    for k in unfold_trans.keys():
                        if k not in str(es):
                            unfold_trans_neg.append(unfold_trans[k])
                    cons_g = get_cons(unfold_trans_neg, sa)
                    unfold_trans_neg.clear()
                    if check_trans(cons_g, current[2], ep['guard'], es['guard'], solve_):
                        pzg_tran = add_transition(current, ep, es, unfold_tran, pa, transitions, working, working_set, sym_)
                        states_cnt = states_cnt + 1
                        transitions_cnt = transitions_cnt + 1
                cons = get_cons(unfold_trans.values(), sa)
                act = set()
                for cloc in sa.clocks :
                    act.add(cloc + ' == ' + CLOCK + str(unfold_tran['from'][1][cloc]) + '_')
                if check_trans(cons, current[2], ep['guard'], act, solve_) :
                    print("guard is not tatualogy : ", 'from : ', current[0], current[1], 'ep : ', ep, 'es :', es)
                    transitions_cnt = transitions_cnt + 1
                    for con in cons :
                        for c in con[21:-1].split(','):
                            if '_p' not in c:
                                continue
                            param_con = compute_parameter_constraints(c, current[2], current[3], ep['guard'], act, unfold_tran, sym_, rsym_, pa, sa, solve_, current[4])
                            parameter_constraints.update(param_con) 
                            if 'False' in param_con and not algo_ter :
                                algo_ter = True
                                print('algorithm terminates time : ', time.time() - start_time)
                                break
    print('transitions count : ', transitions_cnt)
    print('states count : ', states_cnt)
    print('\n****************************\ntotal constraints : ', parameter_constraints)
    print('****************************\n')

        
# files = os.listdir('./')
# for f in files :
#     if '.json' in f :        
#         print(f)
#         # pta = read_from_json('./' + f)
#         pta = read_from_json('./cat1_n.json')
#         pta.validate()
#         start_time = time.time()

#         l_events = {"l"}
#         h_events = {eve for eve in pta.events if eve != 'l'}
#         print(h_events)

#         print("checking non-iterference")
#         inter_time = time.time()
#         ppl = pta.project(l_events)
#         phh = pta.hide(h_events)
#         delta = []
#         # for cloc in pta.clocks:
#         #     delta.append(cloc + ' >= 0')
#         delta.append('_d0_ >= 0')
#         pzg = PZG(ppl.events, [], (ppl.init_loc, [phh.init_loc], delta, delta, 0), [], [])
#         lang_inclusive_check(pzg, ppl, phh, inter_time)
#         print('time for inter : ', time.time() - inter_time)

#         print("checking non-deducibility")
#         dedu_time = time.time()
#         ppl = pta.project(l_events)
#         pph = pta.project(h_events)
#         parallel_ppl_pph = ppl.parallel(pph)
#         delta = []
#         delta.append('_d0_ >= 0')
#         pzg = PZG(parallel_ppl_pph.events, [],(parallel_ppl_pph.init_loc, [pta.init_loc], delta, delta, 0),[], [])
#         lang_inclusive_check(pzg, parallel_ppl_pph, pta, dedu_time)
#         print('time for deduci : ', time.time() - dedu_time)


#         print('complete time : ', time.time() - start_time)
#         break




