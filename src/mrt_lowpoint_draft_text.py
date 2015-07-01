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

import heapq

# simple Class definitions allow structure-like dot notation for 
# variables and a convenient place to initialize those variables.
class Topology:
    pass

class Node:
    pass

class Interface:
    pass

class Bundle:
    pass

class Alternate:
    def __init__(self):
        self.failed_intf = None
        self.nh_list = []
        self.fec = 'NO_ALTERNATE'
        self.prot = 'NO_PROTECTION'
        self.info = 'NONE'


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

def Initialize_Node(node):
    node.intf_list = []
    node.island_intf_list = []
    node.profile_id_list = [0]
    node.GR_sel_priority = 128
    node.IN_MRT_ISLAND = False
    node.IN_GADAG = False
    node.dfs_number = None
    node.dfs_parent = None
    node.dfs_parent_intf = None
    node.dfs_child_list = []
    node.lowpoint_number = None
    node.lowpoint_parent = None
    node.lowpoint_parent_intf = None
    node.localroot = None
    node.block_id = None
    node.IS_CUT_VERTEX = False
    node.blue_next_hops_dict = {}
    node.red_next_hops_dict = {}
    node.pnh_dict = {}
    node.alt_dict = {}
    
def Initialize_Intf(intf):
    intf.metric = None
    intf.area = None
    intf.MRT_INELIGIBLE = False
    intf.IGP_EXCLUDED = False
    intf.UNDIRECTED = True
    intf.INCOMING = False
    intf.OUTGOING = False
    intf.INCOMING_STORED = False
    intf.OUTGOING_STORED = False
    intf.PROCESSED = False
    intf.IN_MRT_ISLAND = False

def Reset_Computed_Node_and_Intf_Values(topo):
    for node in topo.node_list:
        node.IN_MRT_ISLAND = False
        node.IN_GADAG = False
        node.dfs_number = None
        node.dfs_parent = None
        node.dfs_parent_intf = None
        node.dfs_child_list = []
        node.lowpoint_number = None
        node.lowpoint_parent = None
        node.lowpoint_parent_intf = None
        node.localroot = None
        node.block_id = None
        node.IS_CUT_VERTEX = False
        for intf in node.intf_list:
            intf.UNDIRECTED = True
            intf.INCOMING = False
            intf.OUTGOING = False
            intf.INCOMING_STORED = False
            intf.OUTGOING_STORED = False
            intf.IN_MRT_ISLAND = False


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
    topo.gadag_root = None
    topo.node_list = []
    topo.node_dict = {}
    topo.island_node_list = []
    topo.prefix_list = [] # possibly no longer needed
    node_id_set= set()
    cols_list = []
    # on first pass just create nodes
    with open(filename) as topo_file:
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
        Initialize_Node(node)
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
        Initialize_Intf(nodea_intf)
        nodea_intf.metric = metric
        nodea_intf.area = 0
        nodeb_intf = Interface()
        Initialize_Intf(nodeb_intf)
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
            if ( not intf.MRT_INELIGIBLE and not intf.IGP_EXCLUDED 
                 and intf.area == area ):
                if (profile_id in intf.remote_node.profile_id_list):
                    intf.IN_MRT_ISLAND = True
                    if (not intf.remote_node.IN_MRT_ISLAND):
                        intf.remote_node.IN_MRT_ISLAND = True
                        explore_list.append(intf.remote_node)            

def Set_Island_Intf_and_Node_Lists(topo):
    topo.island_node_list = []
    for node in topo.node_list:
        node.island_intf_list = []
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

# addresses these cases.  
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
                bundle.UNDIRECTED = True
                bundle.OUTGOING = False
                bundle.INCOMING = False
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
        
def Store_MRT_NHs_For_One_Src_To_Named_Proxy_Nodes(topo,x):
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        x.blue_next_hops_dict[P.node_id] = []
        x.red_next_hops_dict[P.node_id] = []
        Copy_List_Items(x.blue_next_hops_dict[P.node_id],
                        P.blue_next_hops)
        Copy_List_Items(x.red_next_hops_dict[P.node_id],
                        P.red_next_hops)
        if P.convert_blue_to_green:
            x.blue_to_green_nh_dict[P.node_id] = True
        if P.convert_red_to_green:
            x.red_to_green_nh_dict[P.node_id] = True
        
def Store_Alts_For_One_Src_To_Named_Proxy_Nodes(topo,x):
    for prefix in topo.named_proxy_dict:
        P = topo.named_proxy_dict[prefix]
        x.alt_dict[P.node_id] = []
        Copy_List_Items(x.alt_dict[P.node_id],
                        P.alt_list)               

def Store_Primary_NHs_For_One_Source_To_Nodes(topo,x):
    for y in topo.node_list:
        x.pnh_dict[y.node_id] = []
        Copy_List_Items(x.pnh_dict[y.node_id], y.primary_next_hops)
        
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
        assert(False)   
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
        assert(False) 
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
        assert(False)
    else: # D is unordered wrt S
        if F.HIGHER and F.LOWER:
            if primary_intf.OUTGOING and primary_intf.INCOMING:
                assert(False)
            if primary_intf.OUTGOING:
                # this case isn't hit it topo-9e
                return 'USE_BLUE'
            if primary_intf.INCOMING:
                return 'USE_RED'
            assert(False)
        if F.LOWER:
            return 'USE_RED'
        if F.HIGHER:
            return 'USE_BLUE'
        assert(False)
            
def Select_Alternates(D, F, primary_intf):
    if (D is F) or (D.order_proxy is F):
        return 'PRIM_NH_IS_D_OR_OP_FOR_D'
    D_lower = D.order_proxy.LOWER
    D_higher = D.order_proxy.HIGHER
    D_topo_order = D.order_proxy.topo_order
    return Select_Alternates_Internal(D, F, primary_intf,
                                      D_lower, D_higher, D_topo_order)
      
def Select_Alts_For_One_Src_To_Island_Dests(topo,x):
    Normal_SPF(topo, x)
    for D in topo.island_node_list:
        D.alt_list = []
        if D is x:
            continue
        for primary_intf in D.primary_next_hops:
            alt = Alternate()
            alt.failed_intf = primary_intf
            if primary_intf in x.island_intf_list:
                alt.info = Select_Alternates(D,
                    primary_intf.remote_node, primary_intf)
            else:
                alt.info = 'PRIM_NH_NOT_IN_ISLAND'
                Copy_List_Items(alt.nh_list, D.blue_next_hops)
                alt.fec = 'BLUE'
                alt.prot = 'NODE_PROTECTION'
            if (alt.info == 'USE_BLUE'):                    
                Copy_List_Items(alt.nh_list, D.blue_next_hops)
                alt.fec = 'BLUE'
                alt.prot = 'NODE_PROTECTION'
            if (alt.info == 'USE_RED'):
                Copy_List_Items(alt.nh_list, D.red_next_hops)
                alt.fec = 'RED'
                alt.prot = 'NODE_PROTECTION'
            if (alt.info == 'PRIM_NH_IS_D_OR_OP_FOR_D'):
                if primary_intf.OUTGOING and primary_intf.INCOMING:
                    # cut-link: if there are parallel cut links, use
                    # the link(s) with lowest metric that are not 
                    # primary intf or None
                    cand_alt_list = [None]
                    min_metric = 2147483647
                    for intf in x.island_intf_list:
                        if ( intf is not primary_intf and
                             (intf.remote_node is 
                             primary_intf.remote_node)):
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
                elif primary_intf in D.red_next_hops:
                    Copy_List_Items(alt.nh_list, D.blue_next_hops)
                    alt.fec = 'BLUE'
                    alt.prot = 'LINK_PROTECTION'
                else:
                    Copy_List_Items(alt.nh_list, D.red_next_hops)
                    alt.fec = 'RED'
                    alt.prot = 'LINK_PROTECTION'
            D.alt_list.append(alt) 

def Write_GADAG_To_File(topo, file_prefix):
    gadag_edge_list = []
    for node in topo.island_node_list:
        for intf in node.island_intf_list:
            if intf.OUTGOING:
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
    for node in topo.island_node_list:
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
    for x in topo.island_node_list:
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


def Run_MRT_for_One_Source(topo, src):
    Reset_Computed_Node_and_Intf_Values(topo)
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

def Run_Prim_SPF_for_One_Source(topo,src):
    Normal_SPF(topo, src)
    Store_Primary_NHs_For_One_Source_To_Nodes(topo,src)
    
def Run_MRT_for_All_Sources(topo):
    for src in topo.node_list:
        if 0 in src.profile_id_list:
            # src runs MRT if it has profile_id=0
            Run_MRT_for_One_Source(topo,src)
        else:
            # still run SPF for nodes not running MRT
            Run_Prim_SPF_for_One_Source(topo,src)
            
def Write_Output_To_Files(topo,file_prefix):
    Write_GADAG_To_File(topo,file_prefix)
    Write_Both_MRTs_For_All_Dests_To_File(topo,file_prefix)
    Write_Alternates_For_All_Dests_To_File(topo,file_prefix)

def Create_Example_Topology_Input_File(filename):
    data = [[01,02,10],[02,03,10],[03,04,11],[04,05,10,20],[05,06,10],
            [06,07,10],[06,07,10],[06,07,15],[07,01,10],[07,51,10],
            [51,52,10],[52,53,10],[53,03,10],[01,55,10],[55,06,10],
            [04,12,10],[12,13,10],[13,14,10],[14,15,10],[15,16,10],
            [16,17,10],[17,04,10],[05,76,10],[76,77,10],[77,78,10],
            [78,79,10],[79,77,10]]
    with open(filename, 'w') as topo_file:
        for item in data:
            if len(item) > 3:
                line = (str(item[0])+','+str(item[1])+','+
                        str(item[2])+','+str(item[3])+'\n')
            else:
                line = (str(item[0])+','+str(item[1])+','+
                        str(item[2])+'\n')
            topo_file.write(line)

def Generate_Example_Topology_and_Run_MRT():
    Create_Example_Topology_Input_File('example_topo_input_file.csv')
    topo = Create_Topology_From_File('example_topo_input_file.csv')
    res_file_base = 'example_topo'
    Raise_GADAG_Root_Selection_Priority(topo,3)
    Run_MRT_for_All_Sources(topo)
    Write_Output_To_Files(topo, res_file_base)

Generate_Example_Topology_and_Run_MRT()



