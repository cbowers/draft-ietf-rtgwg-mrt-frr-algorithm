# Copyright (c) 2015, Juniper Networks, Inc.
# All rights reserved.
# 
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#     * Redistributions of source code must retain the above copyright
#       notice, this list of conditions and the following disclaimer.
#     * Redistributions in binary form must reproduce the above copyright
#       notice, this list of conditions and the following disclaimer in the
#       documentation and/or other materials provided with the distribution.
#     * Neither the name of the Juniper Networks nor the
#       names of its contributors may be used to endorse or promote products
#       derived from this software without specific prior written permission.
# 
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS" AND
# ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
# WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL <COPYRIGHT HOLDER> BE LIABLE FOR ANY
# DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
# (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
# SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

# This program has been tested to run on Python 2.6 and 2.7
# (specifically Python 2.6.6 and 2.7.8 were tested).
# The program has known incompatibilities with Python 3.X.

# When executed, this program will generate a text file describing
# an example topology.  It then reads that text file back in as input
# to create the example topology, and runs the MRT algorithm.This 
# was done to simplify the inclusion of the program as a single text 
# file that can be extracted from the IETF draft.

# The output of the program is four text files containing a description
# of the GADAG, the blue and red MRTs for all destinations, and the 
# MRT alternates for all failures. 

import random 
import os.path
import heapq

# simple Class definitions allow structure-like dot notation for 
# variables and a convenient place to initialize those variables.
class Topology:
    def __init__(self):
        self.gadag_root = None
        self.node_list = []
        self.node_dict = {}
        self.test_gr = None
        self.island_node_list_for_test_gr = []
        self.stored_named_proxy_dict = {}
        self.init_new_computing_router()
    def init_new_computing_router(self):
        self.island_node_list = []
        self.named_proxy_dict = {}
        
class Node:
    def __init__(self):
        self.node_id = None
        self.intf_list = []
        self.profile_id_list = [0]
        self.GR_sel_priority = 128
        self.blue_next_hops_dict = {}
        self.red_next_hops_dict = {}
        self.blue_to_green_nh_dict = {}
        self.red_to_green_nh_dict = {}
        self.prefix_cost_dict = {}
        self.pnh_dict = {}
        self.alt_dict = {}
        self.init_new_computing_router()
    def init_new_computing_router(self):        
        self.island_intf_list = []
        self.IN_MRT_ISLAND = False
        self.IN_GADAG = False
        self.dfs_number = None
        self.dfs_parent = None
        self.dfs_parent_intf = None
        self.dfs_child_list = []
        self.lowpoint_number = None
        self.lowpoint_parent = None
        self.lowpoint_parent_intf = None
        self.localroot = None
        self.block_id = None
        self.IS_CUT_VERTEX = False
        self.blue_next_hops = []
        self.red_next_hops = []
        self.primary_next_hops = []
        self.alt_list = []
        
class Interface:
    def __init__(self):
        self.metric = None
        self.area = None
        self.MRT_INELIGIBLE = False
        self.IGP_EXCLUDED = False
        self.SIMULATION_OUTGOING = False
        self.init_new_computing_router()
    def init_new_computing_router(self):
        self.UNDIRECTED = True
        self.INCOMING = False
        self.OUTGOING = False
        self.INCOMING_STORED = False
        self.OUTGOING_STORED = False
        self.IN_MRT_ISLAND = False
        self.PROCESSED = False

class Bundle:
    def __init__(self):
        self.UNDIRECTED = True
        self.OUTGOING = False
        self.INCOMING = False

class Alternate:
    def __init__(self):
        self.failed_intf = None
        self.red_or_blue = None
        self.nh_list = []
        self.fec = 'NO_ALTERNATE'
        self.prot = 'NO_PROTECTION'
        self.info = 'NONE'

class Proxy_Node_Attachment_Router:
    def __init__(self):
        self.prefix = None
        self.node = None
        self.named_proxy_cost = None
        self.min_lfin = None
        self.nh_intf_list = []
        
class Named_Proxy_Node:
    def __init__(self):
        self.node_id = None  #this is the prefix_id
        self.node_prefix_cost_list = []
        self.lfin_list = []
        self.pnar1 = None
        self.pnar2 = None
        self.pnar_X = None
        self.pnar_Y = None
        self.blue_next_hops = []
        self.red_next_hops = []          
        self.primary_next_hops = []
        self.blue_next_hops_dict = {}
        self.red_next_hops_dict = {}
        self.pnh_dict = {}
        self.alt_dict = {}

def Interface_Compare(intf_a, intf_b):
    if intf_a.metric < intf_b.metric:
        return -1
    if intf_b.metric < intf_a.metric:
        return 1
    if intf_a.remote_node.node_id < intf_b.remote_node.node_id:
        return -1
    if intf_b.remote_node.node_id < intf_a.remote_node.node_id:
        return 1    
    return 0

def Sort_Interfaces(topo):
    for node in topo.island_node_list:
        node.island_intf_list.sort(Interface_Compare)

def Reset_Computed_Node_and_Intf_Values(topo):
    topo.init_new_computing_router()
    for node in topo.node_list:
        node.init_new_computing_router()
        for intf in node.intf_list:
            intf.init_new_computing_router()

# This function takes a file with links represented by 2-digit 
# numbers in the format:
# 01,05,10    
# 05,02,30
# 02,01,15 
# which represents a triangle topology with nodes 01, 05, and 02 
# and symmetric metrics of 10, 30, and 15.

# Inclusion of a fourth column makes the metrics for the link
# asymmetric.  An entry of:
# 02,07,10,15
# creates a link from node 02 to 07 with metrics 10 and 15.
def Create_Topology_From_File(filename):
    topo = Topology()
    node_id_set= set()
    cols_list = []
    # on first pass just create nodes
    with open(filename + '.csv') as topo_file:
        for line in topo_file:
            line = line.rstrip('\r\n')
            cols=line.split(',')
            cols_list.append(cols)
            nodea_node_id = int(cols[0])
            nodeb_node_id = int(cols[1])
            if (nodea_node_id > 999 or nodeb_node_id > 999):
                print("node_id must be between 0 and 999.")
                print("exiting.")
                exit()
            node_id_set.add(nodea_node_id)
            node_id_set.add(nodeb_node_id)
    for node_id in node_id_set:
        node = Node()
        node.node_id = node_id
        topo.node_list.append(node)
        topo.node_dict[node_id] = node
    # on second pass create interfaces
    for cols in cols_list:
        nodea_node_id = int(cols[0])
        nodeb_node_id = int(cols[1])
        metric = int(cols[2])
        reverse_metric = int(cols[2])        
        if len(cols) > 3:
            reverse_metric=int(cols[3])
        nodea = topo.node_dict[nodea_node_id]
        nodeb = topo.node_dict[nodeb_node_id]
        nodea_intf = Interface()
        nodea_intf.metric = metric
        nodea_intf.area = 0
        nodeb_intf = Interface()
        nodeb_intf.metric = reverse_metric
        nodeb_intf.area = 0
        nodea_intf.remote_intf = nodeb_intf
        nodeb_intf.remote_intf = nodea_intf
        nodea_intf.remote_node = nodeb
        nodeb_intf.remote_node = nodea
        nodea_intf.local_node = nodea
        nodeb_intf.local_node = nodeb
        nodea_intf.link_data = len(nodea.intf_list)
        nodeb_intf.link_data = len(nodeb.intf_list)
        nodea.intf_list.append(nodea_intf)
        nodeb.intf_list.append(nodeb_intf)
    return topo

def MRT_Island_Identification(topo, computing_rtr, profile_id, area):
    if profile_id in computing_rtr.profile_id_list:
        computing_rtr.IN_MRT_ISLAND = True
        explore_list = [computing_rtr]
    else:
        return
    while explore_list != []:
        next_rtr = explore_list.pop()
        for intf in next_rtr.intf_list:
            if ( (not intf.MRT_INELIGIBLE)
                 and (not intf.remote_intf.MRT_INELIGIBLE)
                 and (not intf.IGP_EXCLUDED) and intf.area == area ):
                if (profile_id in intf.remote_node.profile_id_list):
                    intf.IN_MRT_ISLAND = True
                    intf.remote_intf.IN_MRT_ISLAND = True
                    if (not intf.remote_node.IN_MRT_ISLAND):
                        intf.remote_node.IN_MRT_ISLAND = True
                        explore_list.append(intf.remote_node)

def Compute_Island_Node_List_For_Test_GR(topo, test_gr):
    Reset_Computed_Node_and_Intf_Values(topo)
    topo.test_gr = topo.node_dict[test_gr]
    MRT_Island_Identification(topo, topo.test_gr, 0, 0)
    for node in topo.node_list:
        if node.IN_MRT_ISLAND:
            topo.island_node_list_for_test_gr.append(node)

def Set_Island_Intf_and_Node_Lists(topo):
    for node in topo.node_list:
        if node.IN_MRT_ISLAND:
            topo.island_node_list.append(node)
            for intf in node.intf_list:
                if intf.IN_MRT_ISLAND:
                    node.island_intf_list.append(intf)

global_dfs_number = None

def Lowpoint_Visit(x, parent, intf_p_to_x):
    global global_dfs_number
    x.dfs_number = global_dfs_number
    x.lowpoint_number = x.dfs_number
    global_dfs_number += 1
    x.dfs_parent = parent
    if intf_p_to_x == None:
        x.dfs_parent_intf = None
    else:    
        x.dfs_parent_intf = intf_p_to_x.remote_intf
    x.lowpoint_parent = None
    if parent != None:
        parent.dfs_child_list.append(x)
    for intf in x.island_intf_list:
        if intf.remote_node.dfs_number == None:
            Lowpoint_Visit(intf.remote_node, x, intf)
            if intf.remote_node.lowpoint_number < x.lowpoint_number:
                x.lowpoint_number = intf.remote_node.lowpoint_number
                x.lowpoint_parent = intf.remote_node
                x.lowpoint_parent_intf = intf
        else:
            if intf.remote_node is not parent:
                if intf.remote_node.dfs_number < x.lowpoint_number:
                    x.lowpoint_number = intf.remote_node.dfs_number
                    x.lowpoint_parent = intf.remote_node
                    x.lowpoint_parent_intf = intf

def Run_Lowpoint(topo):
    global global_dfs_number
    global_dfs_number = 0
    Lowpoint_Visit(topo.gadag_root, None, None)

max_block_id = None

def Assign_Block_ID(x, cur_block_id):    
    global max_block_id
    x.block_id = cur_block_id
    for c in x.dfs_child_list:
        if (c.localroot is x):
            max_block_id += 1
            Assign_Block_ID(c, max_block_id)
        else:
            Assign_Block_ID(c, cur_block_id)

def Run_Assign_Block_ID(topo):
    global max_block_id
    max_block_id = 0
    Assign_Block_ID(topo.gadag_root, max_block_id)
            
def Construct_Ear(x, stack, intf, ear_type):
    ear_list = []
    cur_intf = intf
    not_done = True
    while not_done:
        cur_intf.UNDIRECTED = False
        cur_intf.OUTGOING = True
        cur_intf.remote_intf.UNDIRECTED = False
        cur_intf.remote_intf.INCOMING = True
        if cur_intf.remote_node.IN_GADAG == False:
            cur_intf.remote_node.IN_GADAG = True
            ear_list.append(cur_intf.remote_node)
            if ear_type == 'CHILD':
                cur_intf = cur_intf.remote_node.lowpoint_parent_intf
            else:
                assert ear_type == 'NEIGHBOR'
                cur_intf = cur_intf.remote_node.dfs_parent_intf
        else:
            not_done = False
    
    if ear_type == 'CHILD' and cur_intf.remote_node is x:
        # x is a cut-vertex and the local root for the block 
        # in which the ear is computed
        x.IS_CUT_VERTEX = True
        localroot = x
    else:
        # inherit local root from the end of the ear
        localroot = cur_intf.remote_node.localroot
    
    while ear_list != []:
        y = ear_list.pop()
        y.localroot = localroot
        stack.append(y)
        
def Construct_GADAG_via_Lowpoint(topo):
    gadag_root = topo.gadag_root
    gadag_root.IN_GADAG = True
    gadag_root.localroot = None
    stack = []
    stack.append(gadag_root)
    while stack != []:
        x = stack.pop()
        for intf in x.island_intf_list:
            if ( intf.remote_node.IN_GADAG == False 
                 and intf.remote_node.dfs_parent is x ):
                Construct_Ear(x, stack, intf, 'CHILD' )
        for intf in x.island_intf_list:
            if (intf.remote_node.IN_GADAG == False
                and intf.remote_node.dfs_parent is not x):
                Construct_Ear(x, stack, intf, 'NEIGHBOR')
    
def Assign_Remaining_Lowpoint_Parents(topo):
    for node in topo.island_node_list:
        if ( node is not topo.gadag_root
            and node.lowpoint_parent == None ):
            node.lowpoint_parent = node.dfs_parent
            node.lowpoint_parent_intf = node.dfs_parent_intf
            node.lowpoint_number = node.dfs_parent.dfs_number
            
def Add_Undirected_Block_Root_Links(topo):
    for node in topo.island_node_list:
        if node.IS_CUT_VERTEX or node is topo.gadag_root:
            for intf in node.island_intf_list:
                if ( intf.remote_node.localroot is not node 
                     or intf.PROCESSED ):
                    continue
                bundle_list = []
                bundle = Bundle()
                for intf2 in node.island_intf_list:
                    if intf2.remote_node is intf.remote_node:
                        bundle_list.append(intf2)
                        if not intf2.UNDIRECTED:
                            bundle.UNDIRECTED = False
                            if intf2.INCOMING:
                                bundle.INCOMING = True
                            if intf2.OUTGOING:
                                bundle.OUTGOING = True
                if bundle.UNDIRECTED:
                    for intf3 in bundle_list:
                        intf3.UNDIRECTED = False
                        intf3.remote_intf.UNDIRECTED = False
                        intf3.PROCESSED = True
                        intf3.remote_intf.PROCESSED = True
                        intf3.OUTGOING = True
                        intf3.remote_intf.INCOMING = True
                else:
                    if (bundle.OUTGOING and bundle.INCOMING):
                        for intf3 in bundle_list:
                            intf3.UNDIRECTED = False
                            intf3.remote_intf.UNDIRECTED = False
                            intf3.PROCESSED = True
                            intf3.remote_intf.PROCESSED = True
                            intf3.OUTGOING = True
                            intf3.INCOMING = True
                            intf3.remote_intf.INCOMING = True
                            intf3.remote_intf.OUTGOING = True
                    elif bundle.OUTGOING:
                        for intf3 in bundle_list:
                            intf3.UNDIRECTED = False
                            intf3.remote_intf.UNDIRECTED = False
                            intf3.PROCESSED = True
                            intf3.remote_intf.PROCESSED = True
                            intf3.OUTGOING = True
                            intf3.remote_intf.INCOMING = True
                    elif bundle.INCOMING:
                        for intf3 in bundle_list:
                            intf3.UNDIRECTED = False
                            intf3.remote_intf.UNDIRECTED = False
                            intf3.PROCESSED = True
                            intf3.remote_intf.PROCESSED = True
                            intf3.INCOMING = True
                            intf3.remote_intf.OUTGOING = True
                     
def Modify_Block_Root_Incoming_Links(topo):
    for node in topo.island_node_list:
        if ( node.IS_CUT_VERTEX == True or node is topo.gadag_root ):
            for intf in node.island_intf_list:
                if intf.remote_node.localroot is node:
                    if intf.INCOMING:
                        intf.INCOMING = False
                        intf.INCOMING_STORED = True
                        intf.remote_intf.OUTGOING = False
                        intf.remote_intf.OUTGOING_STORED = True

def Revert_Block_Root_Incoming_Links(topo):
    for node in topo.island_node_list:
        if ( node.IS_CUT_VERTEX == True or node is topo.gadag_root ):
            for intf in node.island_intf_list:
                if intf.remote_node.localroot is node:
                    if intf.INCOMING_STORED:
                        intf.INCOMING = True
                        intf.remote_intf.OUTGOING = True
                        intf.INCOMING_STORED = False
                        intf.remote_intf.OUTGOING_STORED = False

def Run_Topological_Sort_GADAG(topo):
    Modify_Block_Root_Incoming_Links(topo)
    for node in topo.island_node_list:
        node.unvisited = 0
        for intf in node.island_intf_list:
            if (intf.INCOMING == True):
                node.unvisited += 1
    working_list = []
    topo_order_list = []
    working_list.append(topo.gadag_root)
    while working_list != []:
        y = working_list.pop(0)
        topo_order_list.append(y)
        for intf in y.island_intf_list:
            if ( intf.OUTGOING == True):
                intf.remote_node.unvisited -= 1
                if intf.remote_node.unvisited == 0:
                    working_list.append(intf.remote_node)
    next_topo_order = 1
    while topo_order_list != []:               
        y = topo_order_list.pop(0)
        y.topo_order = next_topo_order
        next_topo_order += 1
    Revert_Block_Root_Incoming_Links(topo)

def Set_Other_Undirected_Links_Based_On_Topo_Order(topo):
    for node in topo.island_node_list:
        for intf in node.island_intf_list:
            if intf.UNDIRECTED:
                if node.topo_order < intf.remote_node.topo_order:
                    intf.OUTGOING = True
                    intf.UNDIRECTED = False
                    intf.remote_intf.INCOMING = True
                    intf.remote_intf.UNDIRECTED = False
                else:
                    intf.INCOMING = True
                    intf.UNDIRECTED = False
                    intf.remote_intf.OUTGOING = True
                    intf.remote_intf.UNDIRECTED = False 

def Initialize_Temporary_Interface_Flags(topo):
    for node in topo.island_node_list:
        for intf in node.island_intf_list:
            intf.PROCESSED = False
            intf.INCOMING_STORED = False
            intf.OUTGOING_STORED = False
                           
def Add_Undirected_Links(topo):
    Initialize_Temporary_Interface_Flags(topo)
    Add_Undirected_Block_Root_Links(topo)
    Run_Topological_Sort_GADAG(topo)
    Set_Other_Undirected_Links_Based_On_Topo_Order(topo)

def In_Common_Block(x,y):
    if (  (x.block_id == y.block_id)
          or ( x is y.localroot) or (y is x.localroot) ):
        return True
    return False

def Copy_List_Items(target_list, source_list):
    del target_list[:] # Python idiom to remove all elements of a list
    for element in source_list:
        target_list.append(element)

def Add_Item_To_List_If_New(target_list, item):
    if item not in target_list:
        target_list.append(item)

def Store_Results(y, direction):
    if direction == 'INCREASING':
        y.HIGHER = True
        Copy_List_Items(y.blue_next_hops, y.next_hops)
    if direction == 'DECREASING':
        y.LOWER = True
        Copy_List_Items(y.red_next_hops, y.next_hops)
    if direction == 'NORMAL_SPF':
        y.primary_spf_metric = y.spf_metric
        Copy_List_Items(y.primary_next_hops, y.next_hops)
    if direction == 'MRT_ISLAND_SPF':
        Copy_List_Items(y.mrt_island_next_hops, y.next_hops)
    if direction == 'COLLAPSED_SPF':
        y.collapsed_metric = y.spf_metric
        Copy_List_Items(y.collapsed_next_hops, y.next_hops)
                    
# Note that the Python heapq fucntion allows for duplicate items, 
# so we use the 'spf_visited' property to only consider a node 
# as min_node the first time it gets removed from the heap.
def SPF_No_Traverse_Block_Root(topo, spf_root, block_root, direction):
    spf_heap = []
    for y in topo.island_node_list:
        y.spf_metric = 2147483647 # 2^31-1
        y.next_hops = []
        y.spf_visited = False
    spf_root.spf_metric = 0
    heapq.heappush(spf_heap,
                   (spf_root.spf_metric, spf_root.node_id,  spf_root) )
    while spf_heap != []:
        #extract third element of tuple popped from heap
        min_node = heapq.heappop(spf_heap)[2]
        if min_node.spf_visited:
            continue
        min_node.spf_visited = True 
        Store_Results(min_node, direction)
        if ( (min_node is spf_root) or (min_node is not block_root) ):
            for intf in min_node.island_intf_list:
                if ( ( (direction == 'INCREASING' and intf.OUTGOING )
                    or (direction == 'DECREASING' and intf.INCOMING ) )
                    and In_Common_Block(spf_root, intf.remote_node) ) :
                    path_metric = min_node.spf_metric + intf.metric
                    if path_metric < intf.remote_node.spf_metric:
                        intf.remote_node.spf_metric = path_metric
                        if min_node is spf_root:
                            intf.remote_node.next_hops = [intf]
                        else:
                            Copy_List_Items(intf.remote_node.next_hops,
                                            min_node.next_hops)
                        heapq.heappush(spf_heap,
                                       ( intf.remote_node.spf_metric,
                                         intf.remote_node.node_id,
                                         intf.remote_node ) )
                    elif path_metric == intf.remote_node.spf_metric:
                        if min_node is spf_root:
                            Add_Item_To_List_If_New(
                                intf.remote_node.next_hops,intf)
                        else:
                            for nh_intf in min_node.next_hops:
                                Add_Item_To_List_If_New(
                                    intf.remote_node.next_hops,nh_intf)
                    
def Normal_SPF(topo, spf_root):
    spf_heap = []
    for y in topo.node_list:
        y.spf_metric = 2147483647 # 2^31-1 as max metric 
        y.next_hops = []
        y.primary_spf_metric = 2147483647
        y.primary_next_hops = []
        y.spf_visited = False
    spf_root.spf_metric = 0
    heapq.heappush(spf_heap,
                   (spf_root.spf_metric,spf_root.node_id,spf_root) )
    while spf_heap != []:
        #extract third element of tuple popped from heap
        min_node = heapq.heappop(spf_heap)[2] 
        if min_node.spf_visited:
            continue
        min_node.spf_visited = True 
        Store_Results(min_node, 'NORMAL_SPF')
        for intf in min_node.intf_list:
            path_metric = min_node.spf_metric + intf.metric
            if path_metric < intf.remote_node.spf_metric:
                intf.remote_node.spf_metric = path_metric
                if min_node is spf_root:
                    intf.remote_node.next_hops = [intf]
                else:
                    Copy_List_Items(intf.remote_node.next_hops,
                                    min_node.next_hops)
                heapq.heappush(spf_heap,
                               ( intf.remote_node.spf_metric,
                                 intf.remote_node.node_id,
                                 intf.remote_node ) )
            elif path_metric == intf.remote_node.spf_metric:
                if min_node is spf_root:
                    Add_Item_To_List_If_New(
                        intf.remote_node.next_hops,intf)
                else:
                    for nh_intf in min_node.next_hops:
                        Add_Item_To_List_If_New(
                            intf.remote_node.next_hops,nh_intf)

def Set_Edge(y): 
    if (y.blue_next_hops == [] and y.red_next_hops == []):
        Set_Edge(y.localroot)
        Copy_List_Items(y.blue_next_hops,y.localroot.blue_next_hops)
        Copy_List_Items(y.red_next_hops ,y.localroot.red_next_hops)
        y.order_proxy = y.localroot.order_proxy

def Compute_MRT_NH_For_One_Src_To_Island_Dests(topo,x):
    for y in topo.island_node_list:
        y.HIGHER = False
        y.LOWER = False
        y.red_next_hops = []
        y.blue_next_hops = []
        y.order_proxy = y
    SPF_No_Traverse_Block_Root(topo, x, x.localroot, 'INCREASING')
    SPF_No_Traverse_Block_Root(topo, x, x.localroot, 'DECREASING')
    for y in topo.island_node_list:
        if ( y is not x and (y.block_id == x.block_id) ):
            assert (not ( y is x.localroot or x is y.localroot) )
            assert(not (y.HIGHER and y.LOWER) ) 
            if y.HIGHER == True:
                Copy_List_Items(y.red_next_hops,
                                x.localroot.red_next_hops)
            elif y.LOWER == True:
                Copy_List_Items(y.blue_next_hops,
                                x.localroot.blue_next_hops)
            else:
                Copy_List_Items(y.blue_next_hops,
                                x.localroot.red_next_hops)
                Copy_List_Items(y.red_next_hops,
                                x.localroot.blue_next_hops)
        
    # Inherit x's MRT next-hops to reach the GADAG root
    # from x's MRT next-hops to reach its local root,
    # but first check if x is the gadag_root (in which case 
    # x does not have a local root) or if x's local root 
    # is the gadag root (in which case we already have the
    # x's MRT next-hops to reach the gadag root) 
    if x is not topo.gadag_root and x.localroot is not topo.gadag_root:
        Copy_List_Items(topo.gadag_root.blue_next_hops,
                        x.localroot.blue_next_hops)
        Copy_List_Items(topo.gadag_root.red_next_hops,
                        x.localroot.red_next_hops)
        topo.gadag_root.order_proxy = x.localroot
    
    # Inherit next-hops and order_proxies to other blocks   
    for y in topo.island_node_list:
        if (y is not topo.gadag_root and y is not x ):
            Set_Edge(y)
                       
def Store_MRT_Nexthops_For_One_Src_To_Island_Dests(topo,x):
    for y in topo.island_node_list:
        if y is x:
            continue
        x.blue_next_hops_dict[y.node_id] = []
        x.red_next_hops_dict[y.node_id] = []
        Copy_List_Items(x.blue_next_hops_dict[y.node_id],
                        y.blue_next_hops)
        Copy_List_Items(x.red_next_hops_dict[y.node_id],
                        y.red_next_hops)

def Store_Primary_and_Alts_For_One_Src_To_Island_Dests(topo,x):
    for y in topo.island_node_list:
        x.pnh_dict[y.node_id] = []
        Copy_List_Items(x.pnh_dict[y.node_id], y.primary_next_hops)
        x.alt_dict[y.node_id] = []
        Copy_List_Items(x.alt_dict[y.node_id], y.alt_list)
        
def Store_Primary_NHs_For_One_Source_To_Nodes(topo,x):
    for y in topo.node_list:
        x.pnh_dict[y.node_id] = []
        Copy_List_Items(x.pnh_dict[y.node_id], y.primary_next_hops)
       
def Store_MRT_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,x):
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        x.blue_next_hops_dict[P.node_id] = []
        x.red_next_hops_dict[P.node_id] = []
        Copy_List_Items(x.blue_next_hops_dict[P.node_id],
                        P.blue_next_hops)
        Copy_List_Items(x.red_next_hops_dict[P.node_id],
                        P.red_next_hops)
        
def Store_Alts_For_One_Src_To_Named_Proxy_Nodes(topo,x):
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        x.alt_dict[P.node_id] = []
        Copy_List_Items(x.alt_dict[P.node_id],
                        P.alt_list)               
       
def Store_Primary_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,x):
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        x.pnh_dict[P.node_id] = []
        Copy_List_Items(x.pnh_dict[P.node_id],
                        P.primary_next_hops)

def Select_Alternates_Internal(D, F, primary_intf,
                               D_lower, D_higher, D_topo_order):
    if D_higher and D_lower:
        if F.HIGHER and F.LOWER:
            if F.topo_order > D_topo_order:
                return 'USE_BLUE'
            else:
                return 'USE_RED'
        if F.HIGHER:
            return 'USE_RED'
        if F.LOWER:
            return 'USE_BLUE'
        assert(primary_intf.MRT_INELIGIBLE 
               or primary_intf.remote_intf.MRT_INELIGIBLE)
        return 'USE_RED_OR_BLUE'
    if D_higher:
        if F.HIGHER and F.LOWER:
            return 'USE_BLUE'
        if F.LOWER:
            return 'USE_BLUE'
        if F.HIGHER: 
            if (F.topo_order > D_topo_order):
                return 'USE_BLUE'
            if (F.topo_order < D_topo_order):
                return 'USE_RED'
            assert(False)
        assert(primary_intf.MRT_INELIGIBLE 
               or primary_intf.remote_intf.MRT_INELIGIBLE)
        return 'USE_RED_OR_BLUE'
    if D_lower:
        if F.HIGHER and F.LOWER:
            return 'USE_RED'
        if F.HIGHER:
            return 'USE_RED'
        if F.LOWER: 
            if F.topo_order > D_topo_order:
                return 'USE_BLUE'
            if F.topo_order < D_topo_order:
                return 'USE_RED'
            assert(False)        
        assert(primary_intf.MRT_INELIGIBLE 
               or primary_intf.remote_intf.MRT_INELIGIBLE)
        return 'USE_RED_OR_BLUE'
    else: # D is unordered wrt S
        if F.HIGHER and F.LOWER:
            if primary_intf.OUTGOING and primary_intf.INCOMING:
                # This can happen when the primary next hop goes
                # to a node in a different block and D is 
                # unordered wrt S.  
                return 'USE_RED_OR_BLUE'
            if primary_intf.OUTGOING:
                return 'USE_BLUE'
            if primary_intf.INCOMING:
                return 'USE_RED'
            #This can occur when primary_intf is MRT_INELIGIBLE.
            #This appears to be a case where the special 
            #construction of the GADAG allows us to choose red,
            #whereas with an arbitrary GADAG, neither red nor blue
            #is guaranteed to work.  
            assert(primary_intf.MRT_INELIGIBLE 
                   or primary_intf.remote_intf.MRT_INELIGIBLE)
            return 'USE_RED'
        if F.LOWER:
            return 'USE_RED'
        if F.HIGHER:
            return 'USE_BLUE'
        assert(primary_intf.MRT_INELIGIBLE 
               or primary_intf.remote_intf.MRT_INELIGIBLE)
        if F.topo_order > D_topo_order:
            return 'USE_BLUE'
        else:
            return 'USE_RED'

def Select_Alternates(D, F, primary_intf):
    S = primary_intf.local_node
    if not In_Common_Block(F, S):
        return 'PRIM_NH_IN_DIFFERENT_BLOCK'
    if (D is F) or (D.order_proxy is F):
        return 'PRIM_NH_IS_D_OR_OP_FOR_D'
    D_lower = D.order_proxy.LOWER
    D_higher = D.order_proxy.HIGHER
    D_topo_order = D.order_proxy.topo_order
    return Select_Alternates_Internal(D, F, primary_intf,
                                      D_lower, D_higher, D_topo_order)


def Is_Remote_Node_In_NH_List(node, intf_list):
    for intf in intf_list:
        if node is intf.remote_node:
            return True
    return False

def Select_Alts_For_One_Src_To_Island_Dests(topo,x):
    Normal_SPF(topo, x)
    for D in topo.island_node_list:
        D.alt_list = []
        if D is x:
            continue
        for failed_intf in D.primary_next_hops:  
            alt = Alternate()
            alt.failed_intf = failed_intf
            cand_alt_list = []                
            F = failed_intf.remote_node   
            #We need to test if F is in the island, as opposed
            #to just testing if failed_intf is in island_intf_list,
            #because failed_intf could be marked as MRT_INELIGIBLE.
            if F in topo.island_node_list:
                alt.info = Select_Alternates(D, F, failed_intf)
            else:
                #The primary next-hop is not in the MRT Island. 
                #Either red or blue will avoid the primary next-hop,
                #because the primary next-hop is not even in the
                #GADAG.
                alt.info = 'USE_RED_OR_BLUE'
                
            if (alt.info == 'USE_RED_OR_BLUE'):
                alt.red_or_blue = random.choice(['USE_RED','USE_BLUE'])
            if (alt.info == 'USE_BLUE'
                or alt.red_or_blue == 'USE_BLUE'):
                Copy_List_Items(alt.nh_list, D.blue_next_hops)
                alt.fec = 'BLUE'
                alt.prot = 'NODE_PROTECTION'
            if (alt.info == 'USE_RED' or alt.red_or_blue == 'USE_RED'):
                Copy_List_Items(alt.nh_list, D.red_next_hops)
                alt.fec = 'RED'
                alt.prot = 'NODE_PROTECTION'
            if (alt.info == 'PRIM_NH_IN_DIFFERENT_BLOCK'):
                alt.fec = 'NO_ALTERNATE'
                alt.prot = 'NO_PROTECTION'
            if (alt.info == 'PRIM_NH_IS_D_OR_OP_FOR_D'):
                if failed_intf.OUTGOING and failed_intf.INCOMING:
                    # cut-link: if there are parallel cut links, use
                    # the link(s) with lowest metric that are not 
                    # primary intf or None
                    cand_alt_list = [None]
                    min_metric = 2147483647
                    for intf in x.island_intf_list:
                        if ( intf is not failed_intf and
                             (intf.remote_node is 
                             failed_intf.remote_node)):
                            if intf.metric < min_metric:
                                cand_alt_list = [intf]
                                min_metric = intf.metric
                            elif intf.metric == min_metric:
                                cand_alt_list.append(intf)
                    if cand_alt_list != [None]:
                        alt.fec = 'GREEN'
                        alt.prot = 'PARALLEL_CUTLINK'
                    else:
                        alt.fec = 'NO_ALTERNATE'
                        alt.prot = 'NO_PROTECTION'
                    Copy_List_Items(alt.nh_list, cand_alt_list)
                
                # Use Is_Remote_Node_In_NH_List() is used, as opposed
                # to just checking if failed_intf is in D.red_next_hops,
                # because failed_intf could be marked as MRT_INELIGIBLE.
                elif Is_Remote_Node_In_NH_List(F, D.red_next_hops):
                    Copy_List_Items(alt.nh_list, D.blue_next_hops)
                    alt.fec = 'BLUE'
                    alt.prot = 'LINK_PROTECTION'
                else:
                    if not Is_Remote_Node_In_NH_List(F, D.blue_next_hops):
                        print("WEIRD behavior")
                    Copy_List_Items(alt.nh_list, D.red_next_hops)
                    alt.fec = 'RED'
                    alt.prot = 'LINK_PROTECTION'
                  
                # working version but has issue with MRT_INELIGIBLE link being
                # primary_NH  
#                 elif failed_intf in D.red_next_hops:
#                     Copy_List_Items(alt.nh_list, D.blue_next_hops)
#                     alt.fec = 'BLUE'
#                     alt.prot = 'LINK_PROTECTION'
#                 else:
#                     Copy_List_Items(alt.nh_list, D.red_next_hops)
#                     alt.fec = 'RED'
#                     alt.prot = 'LINK_PROTECTION'
            D.alt_list.append(alt)

def Write_GADAG_To_File(topo, file_prefix):
    gadag_edge_list = []
    for node in topo.node_list:
        for intf in node.intf_list:
            if intf.SIMULATION_OUTGOING:
                local_node =  "%04d" % (intf.local_node.node_id)
                remote_node = "%04d" % (intf.remote_node.node_id)
                intf_data = "%03d" % (intf.link_data)
                edge_string=(local_node+','+remote_node+','+
                             intf_data+'\n')
                gadag_edge_list.append(edge_string)
    gadag_edge_list.sort();
    filename = file_prefix + '_gadag.csv'
    with open(filename, 'w') as gadag_file:
        gadag_file.write('local_node,'\
                         'remote_node,local_intf_link_data\n')
        for edge_string in gadag_edge_list:
            gadag_file.write(edge_string);

def Write_MRTs_For_All_Dests_To_File(topo, color, file_prefix):
    edge_list = []
    for node in topo.island_node_list_for_test_gr:
        if color == 'blue':
            node_next_hops_dict = node.blue_next_hops_dict
        elif color == 'red':
            node_next_hops_dict = node.red_next_hops_dict
        for dest_node_id in node_next_hops_dict:
            for intf in node_next_hops_dict[dest_node_id]:
                gadag_root =  "%04d" % (topo.gadag_root.node_id)
                dest_node =  "%04d" % (dest_node_id)
                local_node =  "%04d" % (intf.local_node.node_id)
                remote_node = "%04d" % (intf.remote_node.node_id)
                intf_data = "%03d" % (intf.link_data)
                edge_string=(gadag_root+','+dest_node+','+local_node+
                               ','+remote_node+','+intf_data+'\n')
                edge_list.append(edge_string)
    edge_list.sort()
    filename = file_prefix + '_' + color + '_to_all.csv'
    with open(filename, 'w') as mrt_file:
        mrt_file.write('gadag_root,dest,'\
            'local_node,remote_node,link_data\n')
        for edge_string in edge_list:
            mrt_file.write(edge_string);
            
def Write_Both_MRTs_For_All_Dests_To_File(topo, file_prefix):            
    Write_MRTs_For_All_Dests_To_File(topo, 'blue', file_prefix)
    Write_MRTs_For_All_Dests_To_File(topo, 'red', file_prefix)    

def Write_Alternates_For_All_Dests_To_File(topo, file_prefix):
    edge_list = []
    for x in topo.island_node_list_for_test_gr:
        for dest_node_id in x.alt_dict:
            alt_list = x.alt_dict[dest_node_id]
            for alt in alt_list:
                for alt_intf in alt.nh_list:
                    gadag_root =  "%04d" % (topo.gadag_root.node_id)
                    dest_node =  "%04d" % (dest_node_id)
                    prim_local_node =  \
                        "%04d" % (alt.failed_intf.local_node.node_id)
                    prim_remote_node = \
                        "%04d" % (alt.failed_intf.remote_node.node_id)
                    prim_intf_data = \
                        "%03d" % (alt.failed_intf.link_data)
                    if alt_intf == None:
                        alt_local_node = "None"
                        alt_remote_node = "None"
                        alt_intf_data = "None"
                    else:
                        alt_local_node = \
                            "%04d" % (alt_intf.local_node.node_id)
                        alt_remote_node = \
                            "%04d" % (alt_intf.remote_node.node_id)
                        alt_intf_data = \
                            "%03d" % (alt_intf.link_data)
                    edge_string = (gadag_root+','+dest_node+','+
                        prim_local_node+','+prim_remote_node+','+
                        prim_intf_data+','+alt_local_node+','+
                        alt_remote_node+','+alt_intf_data+','+
                        alt.fec +'\n')
                    edge_list.append(edge_string)
    edge_list.sort()
    filename = file_prefix + '_alts_to_all.csv'
    with open(filename, 'w') as alt_file:
        alt_file.write('gadag_root,dest,'\
            'prim_nh.local_node,prim_nh.remote_node,'\
            'prim_nh.link_data,alt_nh.local_node,'\
            'alt_nh.remote_node,alt_nh.link_data,'\
            'alt_nh.fec\n')
        for edge_string in edge_list:
            alt_file.write(edge_string);

def Raise_GADAG_Root_Selection_Priority(topo,node_id):
    node = topo.node_dict[node_id]
    node.GR_sel_priority = 255
    
def Lower_GADAG_Root_Selection_Priority(topo,node_id):
    node = topo.node_dict[node_id]
    node.GR_sel_priority = 128
 
def GADAG_Root_Compare(node_a, node_b):
    if (node_a.GR_sel_priority > node_b.GR_sel_priority):
        return 1
    elif (node_a.GR_sel_priority < node_b.GR_sel_priority):
        return -1
    else:
        if node_a.node_id > node_b.node_id:
            return 1
        elif node_a.node_id < node_b.node_id:
            return -1

def Set_GADAG_Root(topo,computing_router):
    gadag_root_list = []
    for node in topo.island_node_list:
        gadag_root_list.append(node)
    gadag_root_list.sort(GADAG_Root_Compare)
    topo.gadag_root = gadag_root_list.pop()

def Add_Prefix_Advertisements_From_File(topo, filename):
    prefix_filename = filename + '.prefix'
    cols_list = []
    if not os.path.exists(prefix_filename):
        return
    with open(prefix_filename) as prefix_file:
        for line in prefix_file:
            line = line.rstrip('\r\n')
            cols=line.split(',')
            cols_list.append(cols)
            prefix_id = int(cols[0])
            if prefix_id < 2000 or prefix_id >2999:
                print('skipping the following line of prefix file')
                print('prefix id should be between 2000 and 2999')
                print(line)
                continue
            prefix_node_id = int(cols[1])
            prefix_cost = int(cols[2])
            advertising_node = topo.node_dict[prefix_node_id]
            advertising_node.prefix_cost_dict[prefix_id] = prefix_cost
        
def Add_Prefixes_for_Non_Island_Nodes(topo):
    for node in topo.node_list:
        if node.IN_MRT_ISLAND:
            continue
        prefix_id = node.node_id + 1000
        node.prefix_cost_dict[prefix_id] = 0

def Add_Profile_IDs_from_File(topo, filename):
    profile_filename = filename + '.profile'
    for node in topo.node_list:
        node.profile_id_list = []
    cols_list = []
    if os.path.exists(profile_filename):
        with open(profile_filename) as profile_file:
            for line in profile_file:
                line = line.rstrip('\r\n')
                cols=line.split(',')
                cols_list.append(cols)
                node_id = int(cols[0])
                profile_id = int(cols[1])
                this_node = topo.node_dict[node_id]
                this_node.profile_id_list.append(profile_id)
    else:
        for node in topo.node_list:
            node.profile_id_list = [0]

def Island_Marking_SPF(topo,spf_root):
    spf_root.isl_marking_spf_dict = {}
    for y in topo.node_list:
        y.spf_metric = 2147483647 # 2^31-1 as max metric
        y.PATH_HITS_ISLAND = False
        y.next_hops = []
        y.spf_visited = False
    spf_root.spf_metric = 0
    spf_heap = []
    heapq.heappush(spf_heap,
                   (spf_root.spf_metric,spf_root.node_id,spf_root) )        
    while spf_heap != []:
        #extract third element of tuple popped from heap
        min_node = heapq.heappop(spf_heap)[2] 
        if min_node.spf_visited:
            continue
        min_node.spf_visited = True
        spf_root.isl_marking_spf_dict[min_node.node_id] = \
            (min_node.spf_metric, min_node.PATH_HITS_ISLAND)
        for intf in min_node.intf_list:
            path_metric = min_node.spf_metric + intf.metric
            if path_metric < intf.remote_node.spf_metric:
                intf.remote_node.spf_metric = path_metric
                if min_node is spf_root:
                    intf.remote_node.next_hops = [intf]
                else:
                    Copy_List_Items(intf.remote_node.next_hops,
                                    min_node.next_hops)
                if (intf.remote_node.IN_MRT_ISLAND):
                    intf.remote_node.PATH_HITS_ISLAND = True
                else:
                    intf.remote_node.PATH_HITS_ISLAND = \
                        min_node.PATH_HITS_ISLAND
                heapq.heappush(spf_heap,
                               ( intf.remote_node.spf_metric,
                                 intf.remote_node.node_id,
                                 intf.remote_node ) )
            elif path_metric == intf.remote_node.spf_metric:
                if min_node is spf_root:
                    Add_Item_To_List_If_New(
                        intf.remote_node.next_hops,intf)
                else:
                    for nh_intf in min_node.next_hops:
                        Add_Item_To_List_If_New(
                            intf.remote_node.next_hops,nh_intf)
                if (intf.remote_node.IN_MRT_ISLAND):
                    intf.remote_node.PATH_HITS_ISLAND = True
                else:
                    if (intf.remote_node.PATH_HITS_ISLAND 
                        or min_node.PATH_HITS_ISLAND):
                        intf.remote_node.PATH_HITS_ISLAND = True


def Create_Basic_Named_Proxy_Nodes(topo):
    for node in topo.node_list:
        for prefix in node.prefix_cost_dict:
            prefix_cost = node.prefix_cost_dict[prefix]
            if prefix in topo.named_proxy_dict:
                P = topo.named_proxy_dict[prefix]
                P.node_prefix_cost_list.append((node,prefix_cost))
            else:
                P = Named_Proxy_Node()
                topo.named_proxy_dict[prefix] = P
                P.node_id = prefix
                P.node_prefix_cost_list = [(node,prefix_cost)]

def Compute_Loop_Free_Island_Neighbors_For_Each_Prefix(topo):
    topo.island_nbr_set = set()
    topo.island_border_set = set()
    for node in topo.node_list:
        if node.IN_MRT_ISLAND:
            continue
        for intf in node.intf_list:
            if intf.remote_node.IN_MRT_ISLAND:
                topo.island_nbr_set.add(node)
                topo.island_border_set.add(intf.remote_node)
                
    for island_nbr in topo.island_nbr_set:
        Island_Marking_SPF(topo,island_nbr)
          
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        P.lfin_list = []
        for island_nbr in topo.island_nbr_set:
            min_isl_nbr_to_pref_cost = 2147483647
            for (adv_node, prefix_cost) in P.node_prefix_cost_list:
                (adv_node_cost, path_hits_island) = \
                    island_nbr.isl_marking_spf_dict[adv_node.node_id]
                isl_nbr_to_pref_cost = adv_node_cost + prefix_cost
                if isl_nbr_to_pref_cost < min_isl_nbr_to_pref_cost:
                    min_isl_nbr_to_pref_cost = isl_nbr_to_pref_cost
                    min_path_hits_island = path_hits_island
                elif isl_nbr_to_pref_cost == min_isl_nbr_to_pref_cost:
                    if min_path_hits_island or path_hits_island:
                        min_path_hits_island = True
            if not min_path_hits_island:
                P.lfin_list.append( (island_nbr, 
                                     min_isl_nbr_to_pref_cost) )


def Compute_Island_Border_Router_LFIN_Pairs_For_Each_Prefix(topo):
    for ibr in topo.island_border_set:
        ibr.prefix_lfin_dict = {}
        ibr.min_intf_metric_dict = {}
        ibr.min_intf_list_dict = {}
        ibr.min_intf_list_dict[None] = None
        for intf in ibr.intf_list:
            if not intf.remote_node in topo.island_nbr_set:
                continue
            if not intf.remote_node in ibr.min_intf_metric_dict:
                ibr.min_intf_metric_dict[intf.remote_node] = \
                    intf.metric
                ibr.min_intf_list_dict[intf.remote_node] = [intf]
            else:
                if (intf.metric 
                    < ibr.min_intf_metric_dict[intf.remote_node]):
                    ibr.min_intf_metric_dict[intf.remote_node] = \
                         intf.metric
                    ibr.min_intf_list_dict[intf.remote_node] = [intf]
                elif (intf.metric 
                      < ibr.min_intf_metric_dict[intf.remote_node]):
                    ibr.min_intf_list_dict[intf.remote_node].\
                        append(intf)
    
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        for ibr in topo.island_border_set:
            min_ibr_lfin_pref_cost = 2147483647
            min_lfin = None
            for (lfin, lfin_to_pref_cost) in P.lfin_list:
                if not lfin in ibr.min_intf_metric_dict:
                    continue
                ibr_lfin_pref_cost = \
                    ibr.min_intf_metric_dict[lfin] + lfin_to_pref_cost
                if ibr_lfin_pref_cost < min_ibr_lfin_pref_cost:
                    min_ibr_lfin_pref_cost = ibr_lfin_pref_cost
                    min_lfin = lfin
            ibr.prefix_lfin_dict[prefix] = (min_lfin, 
                min_ibr_lfin_pref_cost,
                ibr.min_intf_list_dict[min_lfin])

def Proxy_Node_Att_Router_Compare(pnar_a, pnar_b):
    if pnar_a.named_proxy_cost < pnar_b.named_proxy_cost:
        return -1
    if pnar_b.named_proxy_cost < pnar_a.named_proxy_cost:
        return 1
    if pnar_a.node.node_id < pnar_b.node.node_id:
        return -1
    if pnar_b.node.node_id < pnar_a.node.node_id:
        return 1
    if pnar_a.min_lfin == None:
        return -1
    if pnar_b.min_lfin == None:
        return 1

def Choose_Proxy_Node_Attachment_Routers(topo):
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        pnar_candidate_list = []
        for (node, prefix_cost) in P.node_prefix_cost_list:
            if not node.IN_MRT_ISLAND:
                continue
            pnar = Proxy_Node_Attachment_Router()
            pnar.prefix = prefix
            pnar.named_proxy_cost = prefix_cost
            pnar.node = node
            pnar_candidate_list.append(pnar)
        for ibr in topo.island_border_set:
            (min_lfin, prefix_cost, min_intf_list) = \
                ibr.prefix_lfin_dict[prefix]
            if min_lfin == None:
                continue
            pnar = Proxy_Node_Attachment_Router()
            pnar.named_proxy_cost = prefix_cost
            pnar.node = ibr
            pnar.min_lfin = min_lfin
            pnar.nh_intf_list = min_intf_list
            pnar_candidate_list.append(pnar)
        pnar_candidate_list.sort(cmp=Proxy_Node_Att_Router_Compare)
        #pop first element from list
        first_pnar = pnar_candidate_list.pop(0) 
        second_pnar = None
        for next_pnar in pnar_candidate_list:
            if next_pnar.node is first_pnar.node:
                continue
            second_pnar = next_pnar
            break
         
        P.pnar1 = first_pnar
        P.pnar2 = second_pnar
     
def Attach_Named_Proxy_Nodes(topo):
    Compute_Loop_Free_Island_Neighbors_For_Each_Prefix(topo)
    Compute_Island_Border_Router_LFIN_Pairs_For_Each_Prefix(topo)
    Choose_Proxy_Node_Attachment_Routers(topo)

def Select_Proxy_Node_NHs(P,S):
    if P.pnar1.node.node_id < P.pnar2.node.node_id:
        X = P.pnar1.node
        Y = P.pnar2.node
    else:
        X = P.pnar2.node
        Y = P.pnar1.node
    P.pnar_X = X
    P.pnar_Y = Y
    A = X.order_proxy
    B = Y.order_proxy
    if (A is S.localroot 
        and B is S.localroot):
        #print("1.0")
        Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
        Copy_List_Items(P.red_next_hops, Y.red_next_hops)
        return
    if (A is S.localroot 
        and B is not S.localroot):
        #print("2.0")
        if B.LOWER:
            #print("2.1")
            Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
            Copy_List_Items(P.red_next_hops, Y.red_next_hops)
            return
        if B.HIGHER:
            #print("2.2")
            Copy_List_Items(P.blue_next_hops, X.red_next_hops)
            Copy_List_Items(P.red_next_hops, Y.blue_next_hops)
            return
        else:
            #print("2.3")
            Copy_List_Items(P.blue_next_hops, X.red_next_hops)
            Copy_List_Items(P.red_next_hops, Y.red_next_hops)
            return           
    if (A is not S.localroot
        and B is S.localroot):
        #print("3.0")
        if A.LOWER:
            #print("3.1")
            Copy_List_Items(P.blue_next_hops, X.red_next_hops)
            Copy_List_Items(P.red_next_hops, Y.blue_next_hops)
            return            
        if A.HIGHER:
            #print("3.2")
            Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
            Copy_List_Items(P.red_next_hops, Y.red_next_hops)
            return
        else:
            #print("3.3")
            Copy_List_Items(P.blue_next_hops, X.red_next_hops)
            Copy_List_Items(P.red_next_hops, Y.red_next_hops)
            return        
    if (A is not S.localroot
        and B is not S.localroot):
        #print("4.0")
        if (S is A.localroot or S is B.localroot):
            #print("4.05")
            if A.topo_order < B.topo_order:
                #print("4.05.1")
                Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
                Copy_List_Items(P.red_next_hops, Y.red_next_hops)
                return
            else:
                #print("4.05.2")
                Copy_List_Items(P.blue_next_hops, X.red_next_hops)
                Copy_List_Items(P.red_next_hops, Y.blue_next_hops)
                return                                 
        if A.LOWER:
            #print("4.1")
            if B.HIGHER:
                #print("4.1.1")
                Copy_List_Items(P.blue_next_hops, X.red_next_hops)
                Copy_List_Items(P.red_next_hops, Y.blue_next_hops)
                return                  
            if B.LOWER:
                #print("4.1.2")
                if A.topo_order < B.topo_order:
                    #print("4.1.2.1")
                    Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
                    Copy_List_Items(P.red_next_hops, Y.red_next_hops)
                    return
                else:
                    #print("4.1.2.2")
                    Copy_List_Items(P.blue_next_hops, X.red_next_hops)
                    Copy_List_Items(P.red_next_hops, Y.blue_next_hops)
                    return                    
            else:
                #print("4.1.3")
                Copy_List_Items(P.blue_next_hops, X.red_next_hops)
                Copy_List_Items(P.red_next_hops, Y.red_next_hops)
                return
        if A.HIGHER:
            #print("4.2")
            if B.HIGHER:
                #print("4.2.1")
                if A.topo_order < B.topo_order:
                    #print("4.2.1.1")
                    Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
                    Copy_List_Items(P.red_next_hops, Y.red_next_hops)   
                    return
                else:
                    #print("4.2.1.2")
                    Copy_List_Items(P.blue_next_hops, X.red_next_hops)
                    Copy_List_Items(P.red_next_hops, Y.blue_next_hops)
                    return                    
            if B.LOWER:
                #print("4.2.2")
                Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
                Copy_List_Items(P.red_next_hops, Y.red_next_hops)   
                return           
            else:
                #print("4.2.3")
                Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
                Copy_List_Items(P.red_next_hops, Y.blue_next_hops) 
                return 
        else:
            #print("4.3")
            if B.LOWER:
                #print("4.3.1")
                Copy_List_Items(P.blue_next_hops, X.red_next_hops)
                Copy_List_Items(P.red_next_hops, Y.red_next_hops) 
                return
            if B.HIGHER:
                #print("4.3.2")
                Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
                Copy_List_Items(P.red_next_hops, Y.blue_next_hops)
                return
            else:
                #print("4.3.3")
                if A.topo_order < B.topo_order:
                    #print("4.3.3.1")
                    Copy_List_Items(P.blue_next_hops, X.blue_next_hops)
                    Copy_List_Items(P.red_next_hops, Y.red_next_hops)
                    return
                else:
                    #print("4.3.3.2")
                    Copy_List_Items(P.blue_next_hops, X.red_next_hops)
                    Copy_List_Items(P.red_next_hops, Y.blue_next_hops)
                    return
    assert(False)
    
def Compute_MRT_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,S):
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        if P.pnar2 == None:
            if S is P.pnar1.node:
                # set the MRT next-hops for the PNAR to 
                # reach the LFIN and change FEC to green
                Copy_List_Items(P.blue_next_hops,
                                P.pnar1.nh_intf_list)
                S.blue_to_green_nh_dict[P.node_id] = True
                Copy_List_Items(P.red_next_hops,
                                P.pnar1.nh_intf_list)
                S.red_to_green_nh_dict[P.node_id] = True
            else:
                # inherit MRT NHs for P from pnar1
                Copy_List_Items(P.blue_next_hops, 
                                P.pnar1.node.blue_next_hops)
                Copy_List_Items(P.red_next_hops, 
                                P.pnar1.node.red_next_hops)
        else:
            Select_Proxy_Node_NHs(P,S)
            # set the MRT next-hops for the PNAR to reach the LFIN 
            # and change FEC to green rely on the red or blue 
            # next-hops being empty to figure out which one needs 
            # to point to the LFIN.
            if S is P.pnar1.node:
                this_pnar = P.pnar1
            elif S is P.pnar2.node:
                this_pnar = P.pnar2
            else:
                continue
            if P.blue_next_hops == []:
                Copy_List_Items(P.blue_next_hops,
                    this_pnar.nh_intf_list)
                S.blue_to_green_nh_dict[P.node_id] = True
            if P.red_next_hops == []:
                Copy_List_Items(P.red_next_hops,
                    this_pnar.nh_intf_list)
                S.red_to_green_nh_dict[P.node_id] = True                   

def Select_Alternates_Proxy_Node(P,F,primary_intf):
    S = primary_intf.local_node
    X = P.pnar_X
    Y = P.pnar_Y
    A = X.order_proxy
    B = Y.order_proxy
    if F is A and F is B:
        return 'PRIM_NH_IS_OP_FOR_BOTH_X_AND_Y'
    if F is A:
        return 'USE_RED'
    if F is B:
        return 'USE_BLUE'
    
    if not In_Common_Block(A, B):
        if In_Common_Block(F, A):
            return 'USE_RED'
        elif In_Common_Block(F, B):
            return 'USE_BLUE'
        else:
            return 'USE_RED_OR_BLUE' 
    if (not In_Common_Block(F, A)
        and not In_Common_Block(F, A) ):
        return 'USE_RED_OR_BLUE'

    alt_to_X = Select_Alternates(X, F, primary_intf)
    alt_to_Y = Select_Alternates(Y, F, primary_intf)

    if (alt_to_X == 'USE_RED_OR_BLUE'
        and alt_to_Y == 'USE_RED_OR_BLUE'):
        return 'USE_RED_OR_BLUE'
    if alt_to_X == 'USE_RED_OR_BLUE':
        return 'USE_BLUE'
    if alt_to_Y == 'USE_RED_OR_BLUE':
        return 'USE_RED'
    
    if (A is S.localroot 
        and B is S.localroot):
        #print("1.0")
        if (alt_to_X == 'USE_BLUE' and alt_to_Y == 'USE_RED'):
            return 'USE_RED_OR_BLUE'
        if alt_to_X == 'USE_BLUE':
            return 'USE_BLUE'
        if alt_to_Y == 'USE_RED':
            return 'USE_RED'
        assert(False)
    if (A is S.localroot 
        and B is not S.localroot):
        #print("2.0")
        if B.LOWER:
            #print("2.1")
            if (alt_to_X == 'USE_BLUE' and alt_to_Y == 'USE_RED'):
                return 'USE_RED_OR_BLUE'
            if alt_to_X == 'USE_BLUE':
                return 'USE_BLUE'
            if alt_to_Y == 'USE_RED':
                return 'USE_RED'
            assert(False)
        if B.HIGHER:
            #print("2.2")
            if (alt_to_X == 'USE_RED' and alt_to_Y == 'USE_BLUE'):
                return 'USE_RED_OR_BLUE'
            if alt_to_X == 'USE_RED':
                return 'USE_BLUE'
            if alt_to_Y == 'USE_BLUE':
                return 'USE_RED'
            assert(False)
        else:
            #print("2.3")
            if (alt_to_X == 'USE_RED' and alt_to_Y == 'USE_RED'):
                return 'USE_RED_OR_BLUE'
            if alt_to_X == 'USE_RED':
                return 'USE_BLUE'
            if alt_to_Y == 'USE_RED':
                return 'USE_RED'
            assert(False)       
    if (A is not S.localroot
        and B is S.localroot):
        #print("3.0")
        if A.LOWER:
            #print("3.1")
            if (alt_to_X == 'USE_RED' and alt_to_Y == 'USE_BLUE'):
                return 'USE_RED_OR_BLUE'
            if alt_to_X == 'USE_RED':
                return 'USE_BLUE'
            if alt_to_Y == 'USE_BLUE':
                return 'USE_RED'
            assert(False)        
        if A.HIGHER:
            #print("3.2")
            if (alt_to_X == 'USE_BLUE' and alt_to_Y == 'USE_RED'):
                return 'USE_RED_OR_BLUE'
            if alt_to_X == 'USE_BLUE':
                return 'USE_BLUE'
            if alt_to_Y == 'USE_RED':
                return 'USE_RED'
            assert(False)
        else:
            #print("3.3")
            if (alt_to_X == 'USE_RED' and alt_to_Y == 'USE_RED'):
                return 'USE_RED_OR_BLUE'
            if alt_to_X == 'USE_RED':
                return 'USE_BLUE'
            if alt_to_Y == 'USE_RED':
                return 'USE_RED'
            assert(False)  
    if (A is not S.localroot
        and B is not S.localroot):
        #print("4.0")
        if (S is A.localroot or S is B.localroot):
            #print("4.05")
            if A.topo_order < B.topo_order:
                #print("4.05.1")
                if (alt_to_X == 'USE_BLUE' and alt_to_Y == 'USE_RED'):
                    return 'USE_RED_OR_BLUE'
                if alt_to_X == 'USE_BLUE':
                    return 'USE_BLUE'
                if alt_to_Y == 'USE_RED':
                    return 'USE_RED'
                assert(False)
            else:
                #print("4.05.2")
                if (alt_to_X == 'USE_RED' and alt_to_Y == 'USE_BLUE'):
                    return 'USE_RED_OR_BLUE'
                if alt_to_X == 'USE_RED':
                    return 'USE_BLUE'
                if alt_to_Y == 'USE_BLUE':
                    return 'USE_RED'
                assert(False)   
        if A.LOWER:
            #print("4.1")
            if B.HIGHER:
                #print("4.1.1")
                if (alt_to_X == 'USE_RED' and alt_to_Y == 'USE_BLUE'):
                    return 'USE_RED_OR_BLUE'
                if alt_to_X == 'USE_RED':
                    return 'USE_BLUE'
                if alt_to_Y == 'USE_BLUE':
                    return 'USE_RED'
                assert(False)                 
            if B.LOWER:
                #print("4.1.2")
                if A.topo_order < B.topo_order:
                    #print("4.1.2.1")
                    if (alt_to_X == 'USE_BLUE' 
                        and alt_to_Y == 'USE_RED'):
                        return 'USE_RED_OR_BLUE'
                    if alt_to_X == 'USE_BLUE':
                        return 'USE_BLUE'
                    if alt_to_Y == 'USE_RED':
                        return 'USE_RED'
                    assert(False)
                else:
                    #print("4.1.2.2")
                    if (alt_to_X == 'USE_RED' 
                        and alt_to_Y == 'USE_BLUE'):
                        return 'USE_RED_OR_BLUE'
                    if alt_to_X == 'USE_RED':
                        return 'USE_BLUE'
                    if alt_to_Y == 'USE_BLUE':
                        return 'USE_RED'
                    assert(False)  
            else:
                #print("4.1.3")
                if (F.LOWER and not F.HIGHER
                    and F.topo_order > A.topo_order):
                    #print("4.1.3.1")
                    return 'USE_RED'
                else:
                    #print("4.1.3.2")
                    return 'USE_BLUE'        
        if A.HIGHER:
            #print("4.2")
            if B.HIGHER:
                #print("4.2.1")
                if A.topo_order < B.topo_order:
                    #print("4.2.1.1")
                    if (alt_to_X == 'USE_BLUE' 
                        and alt_to_Y == 'USE_RED'):
                        return 'USE_RED_OR_BLUE'
                    if alt_to_X == 'USE_BLUE':
                        return 'USE_BLUE'
                    if alt_to_Y == 'USE_RED':
                        return 'USE_RED'
                    assert(False)
                else:
                    #print("4.2.1.2")
                    if (alt_to_X == 'USE_RED' 
                        and alt_to_Y == 'USE_BLUE'):
                        return 'USE_RED_OR_BLUE'
                    if alt_to_X == 'USE_RED':
                        return 'USE_BLUE'
                    if alt_to_Y == 'USE_BLUE':
                        return 'USE_RED'
                    assert(False)
            if B.LOWER:
                #print("4.2.2")
                if (alt_to_X == 'USE_BLUE' 
                    and alt_to_Y == 'USE_RED'):
                    return 'USE_RED_OR_BLUE'
                if alt_to_X == 'USE_BLUE':
                    return 'USE_BLUE'
                if alt_to_Y == 'USE_RED':
                    return 'USE_RED'
                assert(False)      
            else:
                #print("4.2.3")
                if (F.HIGHER and not F.LOWER
                    and F.topo_order < A.topo_order):
                    return 'USE_RED'
                else:
                    return 'USE_BLUE'                                
        else:
            #print("4.3")
            if B.LOWER:
                #print("4.3.1")
                if (F.LOWER and not F.HIGHER
                    and F.topo_order > B.topo_order):
                    return 'USE_BLUE'
                else:
                    return 'USE_RED'
            if B.HIGHER:
                #print("4.3.2")
                if (F.HIGHER and not F.LOWER
                    and F.topo_order < B.topo_order):
                    return 'USE_BLUE'
                else:
                    return 'USE_RED'
            else:
                #print("4.3.3")
                if A.topo_order < B.topo_order:
                    #print("4.3.3.1")
                    if (alt_to_X == 'USE_BLUE' 
                        and alt_to_Y == 'USE_RED'):
                        return 'USE_RED_OR_BLUE'
                    if alt_to_X == 'USE_BLUE':
                        return 'USE_BLUE'
                    if alt_to_Y == 'USE_RED':
                        return 'USE_RED'
                    assert(False)
                else:
                    #print("4.3.3.2")
                    if (alt_to_X == 'USE_RED' 
                        and alt_to_Y == 'USE_BLUE'):
                        return 'USE_RED_OR_BLUE'
                    if alt_to_X == 'USE_RED':
                        return 'USE_BLUE'
                    if alt_to_Y == 'USE_BLUE':
                        return 'USE_RED'
                    assert(False)                 
    assert(False)

def Compute_Primary_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,src):            
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        min_total_pref_cost = 2147483647
        for (adv_node, prefix_cost) in P.node_prefix_cost_list:
            total_pref_cost = (adv_node.primary_spf_metric 
                               + prefix_cost)
            if total_pref_cost < min_total_pref_cost:
                min_total_pref_cost = total_pref_cost
                Copy_List_Items(P.primary_next_hops,
                                adv_node.primary_next_hops)
            elif total_pref_cost == min_total_pref_cost:
                for nh_intf in adv_node.primary_next_hops:
                    Add_Item_To_List_If_New(P.primary_next_hops,
                                            nh_intf)

def Select_Alts_For_One_Src_To_Named_Proxy_Nodes(topo,src):
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        P.alt_list = []
        for failed_intf in P.primary_next_hops:
            alt = Alternate()
            alt.failed_intf = failed_intf
            if failed_intf not in src.island_intf_list:
                alt.info = 'PRIM_NH_FOR_PROXY_NODE_NOT_IN_ISLAND'
            elif P.pnar1 is None:
                alt.info = 'NO_PNARs_EXIST_FOR_THIS_PREFIX'
            elif src is P.pnar1.node:
                alt.info = 'SRC_IS_PNAR'
            elif P.pnar2 is not None and src is P.pnar2.node:
                alt.info = 'SRC_IS_PNAR'
            elif P.pnar2 is None:
                #inherit alternates from the only pnar.
                alt.info = Select_Alternates(P.pnar1.node, 
                            failed_intf.remote_node, failed_intf)
            elif failed_intf in src.island_intf_list:
                alt.info = Select_Alternates_Proxy_Node(P,
                            failed_intf.remote_node, failed_intf)
        
            if alt.info == 'USE_RED_OR_BLUE':
                alt.red_or_blue = \
                    random.choice(['USE_RED','USE_BLUE'])
            if (alt.info == 'USE_BLUE' 
                or alt.red_or_blue == 'USE_BLUE'):
                Copy_List_Items(alt.nh_list, P.blue_next_hops)
                alt.fec = 'BLUE'
                alt.prot = 'NODE_PROTECTION'
            elif (alt.info == 'USE_RED' 
                  or alt.red_or_blue == 'USE_RED'):
                Copy_List_Items(alt.nh_list, P.red_next_hops)
                alt.fec = 'RED'
                alt.prot = 'NODE_PROTECTION'
            elif (alt.info == 'PRIM_NH_IS_D_OR_OP_FOR_D' 
                or alt.info == 'PRIM_NH_IS_OP_FOR_BOTH_X_AND_Y'):
                if failed_intf.OUTGOING and failed_intf.INCOMING:
                    # cut-link: if there are parallel cut links, use
                    # the link(s) with lowest metric that are not 
                    # primary intf or None
                    cand_alt_list = [None]
                    min_metric = 2147483647
                    for intf in src.island_intf_list:
                        if ( intf is not failed_intf and
                             (intf.remote_node is 
                             failed_intf.remote_node)):
                            if intf.metric < min_metric:
                                cand_alt_list = [intf]
                                min_metric = intf.metric
                            elif intf.metric == min_metric:
                                cand_alt_list.append(intf)
                    if cand_alt_list != [None]:
                        alt.fec = 'GREEN'
                        alt.prot = 'PARALLEL_CUTLINK'
                    else:
                        alt.fec = 'NO_ALTERNATE'
                        alt.prot = 'NO_PROTECTION'
                    Copy_List_Items(alt.nh_list, cand_alt_list)
                else:
                    # set Z as the node to inherit blue next-hops from
                    if alt.info == 'PRIM_NH_IS_D_OR_OP_FOR_D':
                        Z = P.pnar1.node
                    else:
                        Z = P
                    if failed_intf in Z.red_next_hops:
                        Copy_List_Items(alt.nh_list, Z.blue_next_hops)
                        alt.fec = 'BLUE'
                        alt.prot = 'LINK_PROTECTION'
                    else:
                        assert(failed_intf in Z.blue_next_hops)
                        Copy_List_Items(alt.nh_list, Z.red_next_hops)
                        alt.fec = 'RED'
                        alt.prot = 'LINK_PROTECTION'

            elif alt.info == 'PRIM_NH_FOR_PROXY_NODE_NOT_IN_ISLAND':
                if (P.pnar2 == None and src is P.pnar1.node):
                    #MRT Island is singly connected to non-island dest
                    alt.fec = 'NO_ALTERNATE'
                    alt.prot = 'NO_PROTECTION'
                elif P.node_id in src.blue_to_green_nh_dict:
                    # blue to P goes to failed LFIN so use red to P
                    Copy_List_Items(alt.nh_list, P.red_next_hops)
                    alt.fec = 'RED'
                    alt.prot = 'LINK_PROTECTION'
                elif P.node_id in src.red_to_green_nh_dict:
                    # red to P goes to failed LFIN so use blue to P
                    Copy_List_Items(alt.nh_list, P.blue_next_hops)
                    alt.fec = 'BLUE'
                    alt.prot = 'LINK_PROTECTION'
                else:
                    Copy_List_Items(alt.nh_list, P.blue_next_hops)
                    alt.fec = 'BLUE'
                    alt.prot = 'LINK_PROTECTION'
            elif alt.info == 'TEMP_NO_ALTERNATE':
                alt.fec = 'NO_ALTERNATE'
                alt.prot = 'NO_PROTECTION'

            P.alt_list.append(alt)

def Run_Basic_MRT_for_One_Source(topo, src):
    MRT_Island_Identification(topo, src, 0, 0)
    Set_Island_Intf_and_Node_Lists(topo)
    Set_GADAG_Root(topo,src)
    Sort_Interfaces(topo)
    Run_Lowpoint(topo)
    Assign_Remaining_Lowpoint_Parents(topo)
    Construct_GADAG_via_Lowpoint(topo)
    Run_Assign_Block_ID(topo)
    Add_Undirected_Links(topo)
    Compute_MRT_NH_For_One_Src_To_Island_Dests(topo,src)
    Store_MRT_Nexthops_For_One_Src_To_Island_Dests(topo,src)
    Select_Alts_For_One_Src_To_Island_Dests(topo,src)
    Store_Primary_and_Alts_For_One_Src_To_Island_Dests(topo,src)

def Store_GADAG_and_Named_Proxies_Once(topo):
    for node in topo.node_list:
        for intf in node.intf_list:
            if intf.OUTGOING:
                intf.SIMULATION_OUTGOING = True
            else:
                intf.SIMULATION_OUTGOING = False
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        topo.stored_named_proxy_dict[prefix] = P
    
def Run_Basic_MRT_for_All_Sources(topo):
    for src in topo.node_list:
        Reset_Computed_Node_and_Intf_Values(topo)
        Run_Basic_MRT_for_One_Source(topo,src)
        if src is topo.gadag_root:
            Store_GADAG_and_Named_Proxies_Once(topo)

def Run_MRT_for_One_Source(topo, src):
    MRT_Island_Identification(topo, src, 0, 0)
    Set_Island_Intf_and_Node_Lists(topo)
    Set_GADAG_Root(topo,src)
    Sort_Interfaces(topo)
    Run_Lowpoint(topo)
    Assign_Remaining_Lowpoint_Parents(topo)
    Construct_GADAG_via_Lowpoint(topo)
    Run_Assign_Block_ID(topo)
    Add_Undirected_Links(topo)
    Compute_MRT_NH_For_One_Src_To_Island_Dests(topo,src)
    Store_MRT_Nexthops_For_One_Src_To_Island_Dests(topo,src)
    Select_Alts_For_One_Src_To_Island_Dests(topo,src)
    Store_Primary_and_Alts_For_One_Src_To_Island_Dests(topo,src)
    Create_Basic_Named_Proxy_Nodes(topo) 
    Attach_Named_Proxy_Nodes(topo) 
    Compute_MRT_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,src) 
    Store_MRT_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,src) 
    Compute_Primary_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,src) 
    Store_Primary_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,src) 
    Select_Alts_For_One_Src_To_Named_Proxy_Nodes(topo,src) 
    Store_Alts_For_One_Src_To_Named_Proxy_Nodes(topo,src) 

def Run_Prim_SPF_for_One_Source(topo,src):
    Normal_SPF(topo, src)
    Store_Primary_NHs_For_One_Source_To_Nodes(topo,src)
    Create_Basic_Named_Proxy_Nodes(topo) 
    Compute_Primary_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,src) 
    Store_Primary_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,src) 
       
def Run_MRT_for_All_Sources(topo):
    for src in topo.node_list:
        Reset_Computed_Node_and_Intf_Values(topo)
        if src in topo.island_node_list_for_test_gr:
            # src runs MRT if it is in same MRT island as test_gr
            Run_MRT_for_One_Source(topo,src)
            if src is topo.gadag_root:
                Store_GADAG_and_Named_Proxies_Once(topo)
        else:
            # src still runs SPF if not in MRT island
            Run_Prim_SPF_for_One_Source(topo,src)
            
def Write_Output_To_Files(topo,file_prefix):
    Write_GADAG_To_File(topo,file_prefix)
    Write_Both_MRTs_For_All_Dests_To_File(topo,file_prefix)
    Write_Alternates_For_All_Dests_To_File(topo,file_prefix)

def Create_Basic_Topology_Input_File(filename):
    data = [[01,02,10],[02,03,10],[03,04,11],[04,05,10,20],[05,06,10],
            [06,07,10],[06,07,10],[06,07,15],[07,01,10],[07,51,10],
            [51,52,10],[52,53,10],[53,03,10],[01,55,10],[55,06,10],
            [04,12,10],[12,13,10],[13,14,10],[14,15,10],[15,16,10],
            [16,17,10],[17,04,10],[05,76,10],[76,77,10],[77,78,10],
            [78,79,10],[79,77,10]]
    with open(filename + '.csv', 'w') as topo_file:
        for item in data:
            if len(item) > 3:
                line = (str(item[0])+','+str(item[1])+','+
                        str(item[2])+','+str(item[3])+'\n')
            else:
                line = (str(item[0])+','+str(item[1])+','+
                        str(item[2])+'\n')
            topo_file.write(line)

def Create_Complex_Topology_Input_File(filename):
    data = [[01,02,10],[02,03,10],[03,04,11],[04,05,10,20],[05,06,10],
            [06,07,10],[06,07,10],[06,07,15],[07,01,10],[07,51,10],
            [51,52,10],[52,53,10],[53,03,10],[01,55,10],[55,06,10],
            [04,12,10],[12,13,10],[13,14,10],[14,15,10],[15,16,10],
            [16,17,10],[17,04,10],[05,76,10],[76,77,10],[77,78,10],
            [78,79,10],[79,77,10]]
    with open(filename + '.csv', 'w') as topo_file:
        for item in data:
            if len(item) > 3:
                line = (str(item[0])+','+str(item[1])+','+
                        str(item[2])+','+str(item[3])+'\n')
            else:
                line = (str(item[0])+','+str(item[1])+','+
                        str(item[2])+'\n')
            topo_file.write(line)
            
    data = [[01,0],[02,0],[03,0],[04,0],[05,0],
            [06,0],[07,0],
            [51,0],[55,0],
            [12,0],[13,0],[14,0],[15,0],
            [16,0],[17,0],[76,0],[77,0],
            [78,0],[79,0]]
    with open(filename + '.profile', 'w') as topo_file:
        for item in data:
            line = (str(item[0])+','+str(item[1])+'\n')
            topo_file.write(line)
            
    data = [[2001,05,100],[2001,07,120],[2001,03,130],
            [2002,13,100],[2002,15,110],
            [2003,52,100],[2003,78,100]]
    with open(filename + '.prefix', 'w') as topo_file:
        for item in data:
            line = (str(item[0])+','+str(item[1])+','+
                    str(item[2])+'\n')
            topo_file.write(line)         

def Generate_Basic_Topology_and_Run_MRT():
    this_gadag_root = 3
    Create_Basic_Topology_Input_File('basic_topo_input')
    topo = Create_Topology_From_File('basic_topo_input')
    res_file_base = 'basic_topo'
    Compute_Island_Node_List_For_Test_GR(topo, this_gadag_root)
    Raise_GADAG_Root_Selection_Priority(topo,this_gadag_root)
    Run_Basic_MRT_for_All_Sources(topo)
    Write_Output_To_Files(topo, res_file_base)
    
def Generate_Complex_Topology_and_Run_MRT():
    this_gadag_root = 3
    Create_Complex_Topology_Input_File('complex_topo_input')
    topo = Create_Topology_From_File('complex_topo_input')
    Add_Profile_IDs_from_File(topo,'complex_topo_input')
    Add_Prefix_Advertisements_From_File(topo,'complex_topo_input')
    Compute_Island_Node_List_For_Test_GR(topo, this_gadag_root)
    Add_Prefixes_for_Non_Island_Nodes(topo)
    res_file_base = 'complex_topo'
    Raise_GADAG_Root_Selection_Priority(topo,this_gadag_root)
    Run_MRT_for_All_Sources(topo)
    Write_Output_To_Files(topo, res_file_base)

Generate_Basic_Topology_and_Run_MRT()
 
Generate_Complex_Topology_and_Run_MRT()

