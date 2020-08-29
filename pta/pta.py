#!/usr/bin/env python3
"""Classes and methods for working with pta."""

import copy
import itertools
import queue

import automata.base.exceptions as exceptions
import automata.fa.fa as fa

from itertools import product

from z3 import *


class PTA(fa.FA) :
    def __init__(self, events, locations, init_loc, clocks, parameters, invariants, edges, param_inv):
        self.events = events.copy()
        self.locations = locations.copy()
        self.init_loc = init_loc
        self.clocks = clocks.copy()
        self.parameters = parameters.copy()
        self.invariants = invariants.copy()
        self.edges = copy.deepcopy(edges)
        self.param_inv = param_inv.copy()

    """projection of self pta on event"""
    def project(self, event) :
        automata = self.copy()
        edges = automata.edges.copy()
        for e in automata.edges : 
            if e['event'] not in event :
                e['event'] = "tao"
        automata.edges = edges
        events = automata.events.copy()
        for eve in events : 
            if eve not in event :
                automata.events.remove(eve)
        automata.validate()
        automata.minify()
        return automata

    """hide event in self pta"""
    def hide(self, event) :
        automata = self.copy()
        edges = automata.edges.copy()
        for e in automata.edges :
            if e['event'] in event :
                edges.remove(e)
        events = automata.events.copy()
        for eve in event :
            automata.events.remove(eve)
        automata.edges = edges
        automata.validate()
        automata.minify()
        return automata

    """remove unreachabel edges in self pta"""
    def minify(self) :
        reachable = {self.init_loc}
        edges = self.edges.copy()
        for e in self.edges :
            if e['from'] in reachable :
                reachable.add(e['to'])
        for e in self.edges : 
            if e['from'] not in reachable :
                edges.remove(e)
        self.edges = edges

    """parallel between self and s, the order matters"""
    def parallel(self, s):
        p = self.copy()
        events = set(p.events)
        events.update(s.events)
        events = list(events)
        events_intersetion = []
        for e in p.events :
            if e in s.events:
                events_intersetion.append(e)

        locations = list(product(p.locations, s.locations))
        # clocks = list(product(p.clocks, s.clocks))
        clocks = set(p.clocks)
        clocks.update(s.clocks)
        clocks = list(clocks)

        init_loc = (p.init_loc, s.init_loc)

        parameters = set(p.parameters)
        parameters.update(s.parameters)
        parameters = list(parameters) 

        invariants = []    
        for l in locations :
            pl = l[0]
            sl = l[1]  
            for pinv in p.invariants : 
                if pl in pinv :
                    break
            invariant = pinv[pl].copy()
            for sinv in s.invariants :
                if sl in sinv: 
                    break
            for inv in sinv[sl] :
                invariant.append(inv)
            invariant = list(dict.fromkeys(invariant))
            invariants.append({l:invariant})

        edges = []
        for l in locations :
            pl = l[0]
            sl = l[1]
            for pe in p.edges :
                if pl == pe['from'] :
                   for se in s.edges :
                       if sl == se['from'] and se['event'] == pe['event'] and se['event'] in events_intersetion:
                           for g in se['guard'] : 
                               pe['guard'].append(g)
                           guard = list(dict.fromkeys(pe['guard']))
                           for c in se['clock'] : 
                               pe['clock'].append(c)
                           clock = list(dict.fromkeys(pe['clock']))
                           obj = {'from' : l, 'to' : (pe['to'], se['to']), 'event' : pe['event'], 'guard' : guard, 'clock' : clock}
                           edges.append(obj)
        for l in locations :
            pl = l[0]
            sl = l[1]
            for pe in p.edges :
                if pl == pe['from'] and pe['event'] not in events_intersetion :
                    obj = {'from' : l, 'to' : (pe['to'], sl), 'event' : pe['event'], 'guard' : pe['guard'], 'clock' : pe['clock']}
                    edges.append(obj)
            for se in s.edges :
                if sl == se['from'] and se['event'] not in events_intersetion : 
                    obj = {'from' : l, 'to' : (pl, se['to']), 'event' : se['event'], 'guard' : se['guard'], 'clock' : se['clock']}
                    edges.append(obj)

        param_inv = set()
        for pi in p.param_inv :
            param_inv.add(pi)
        for si in s.param_inv :
            param_inv.add(si)
        ret = PTA(events, locations, init_loc, clocks, parameters, invariants, edges, list(param_inv))
        ret.minify()
        return ret
                     
    def read_input_stepwise(self, input_str):
        """
        Check if the given string is accepted by this DFA.

        Yield the current configuration of the DFA at each step.
        """
       

    def validate(self):
        """ check if all edges are valid
        """
        for e in self.edges :
            if e['event'] !=  'tao' and e['event'] not in self.events :
                print("invalid events")
                return False
            if e['from'] not in self.locations :
                print("invalid locations : ", e['from'])
                return False
            if e['to'] not in self.locations :
                print("invalid locations : ", e['to'])
                return False
            for c in e['clock'] :
                if c not in self.clocks :
                    print("invalid clocks")
                    return False
        return True
    
    def print (self) :
        print("events : " , self.events)
        print("locations : ", self.locations)
        print("init loc : ", self.init_loc)
        print("clocks : ", self.clocks)
        print("paramenters : ", self.parameters)
        print("invariants : ")
        for inv in self.invariants :
            print(inv)
        print("edges : ")
        for e in self.edges :
            print(e)

class PZG(fa.FA) :
    def validate(self) :
        return True
    def read_input_stepwise(self, input_str):
        True

    def __init__(self, events, states, init_state, transitions=[], clocks=[]) :
        self.events = events
        self.states = states
        self.init_state = init_state
        self.transitions = transitions
        self.clocks = clocks
    
    def print(self) :
        print('events : ', self.events)
        print('states : ')
        for s in self.states :
            print(s)
        print('init state : ', self.init_state)
        print('transitions : ')
        for trans in self.transitions : 
            print(trans)

"""unfolding the spec automata"""
class UNFOLDS(fa.FA) :
    def validate(self) :
        return True
    def read_input_stepwise(self, input_str):
        return True

    def __init__(self, locations, init_loc, clocks, edges) :
        self.locations = locations
        self.init_loc = init_loc
        self.clocks = clocks
        self.edges = edges
    
    def minify(self) :
        unfolding_edges_dict = {}
        for e in self.edges :
            unfolding_edges_dict[(e['from'][0], tuple(e['from'][1].keys()), e['from'][2], e['to'][0], tuple(e['to'][1].keys()), e['to'][2])] = e
        self.edges = []
        for e in unfolding_edges_dict.keys() :
            self.edges.append(unfolding_edges_dict[e])



 