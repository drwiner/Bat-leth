from OrderingGraph import OrderingGraph, CausalLinkGraph
from Flaws import Flaw, FlawLib
from uuid import uuid1 as uid
import itertools
from clockdeco import clock
from Element import Argument, Element, Operator, Literal
from Graph import Edge
from ElementGraph import ElementGraph
from Reuse import ReuseLib
from GlobalContainer import GC
import copy
import collections

class Action(ElementGraph):
	#stepnumber = 2
	def __init__(self, ID=None, type_graph=None, name=None, Elements=None, root_element=None, Edges=None):

		if type_graph is None:
			type_graph = 'Action'

		if Edges is None:
			Edges = set()

		if root_element is None:
			root_element = Operator()
			
		if Elements is None:
			Elements = {root_element}

		self.nonequals = set()
			
		super(Action,self).__init__(ID, type_graph, name, Elements, root_element, Edges)

	def __hash__(self):
		return hash(arg for arg in self.Args) ^ hash(self.root.name)

	def __eq__(self, other):
		if not isinstance(other, ElementGraph):
			return False
		if self.root.name == other.root.name:
				if self.Args == other.Args:
					return True
		return False

	# @property
	# def executed(self):
	# 	return self.root.executed

	def RemoveSubgraph(self, elm):
		elm = self.getElementById(elm.ID)

		if isinstance(elm, Literal):
			self.elements.remove(elm)

		link = None
		for edge in list(self.edges):
			if edge.source == elm:
				self.edges.remove(edge)
			if link is None:
				if edge.sink == elm:
					link = edge
		return link

	def getPreconditionsOrEffects(self, label):
		return {edge.sink for edge in self.edges if edge.label == label}

	def __getattr__(self, name):
		if name == 'preconditions':
			self.preconditions = self.getPreconditionsOrEffects('precond-of')
			return self.preconditions
		elif name == 'effects':
			self.effects = self.getPreconditionsOrEffects('effect-of')
			return self.effects
		elif name == 'Args':
			self.updateArgs()
			return self.Args
		else:
			raise AttributeError('no attribute {}'.format(name))

	@property
	def stepnumber(self):
		return self.root.stepnumber

	def replaceInternals(self):
		self.ID = uid(self.root.stepnumber)
		for elm in self.elements:
			if not isinstance(elm, Argument):
				elm.ID = uid(self.root.stepnumber)


	def _replaceInternals(self):
		self.ID = uid(self.root.stepnumber)
		for elm in self.elements:
			if not isinstance(elm, Argument):
				elm.replaced_ID = uid(self.root.stepnumber)

	def deepcopy(self, replace_internals=False):
		new_self = copy.deepcopy(self)
		if replace_internals:
			new_self.replaceInternals()
		return new_self


	# '''for debugging'''
	# def getConditions(self):
		# pres = {edge for edge in self.edges if edge.label == 'precond-of'}
		# effs = {edge for edge in self.edges if edge.label == 'effect-of'}
		# print('Preconditions:\n')
		# for pre in pres:
			# pre.sink
		# print('Effects:\n')
		# for eff in effs:
			# eff.sink

	def isConsistent(self, other):
		""" an action is consistent just when one can absolve the other"""
		if isinstance(other, ElementGraph):
			return self.isConsistentSubgraph(other)
		if isinstance(other, Operator):
			return self.root.isConsistent(other)

		
	def __repr__(self):
		self.updateArgs()
		args = str(self.Args)
		if hasattr(self.root, 'executed'):
			exe = self.root.executed
			if exe is None:
				exe = 'ex'
		else:
			exe = 'ex'
		id = str(self.root.ID)[19:23]
		return '{}-{}-{}-{}'.format(exe, self.root.name, self.root.stepnumber,id) + args

		
class Condition(ElementGraph):
	""" A Literal used in causal link"""
	def __init__(self, ID=None, type_graph=None, name=None, Elements=None, root_element=None, Edges=None,
				 Restrictions=None):
		if type_graph is None:
			type_graph = 'Condition'
		
		super(Condition,self).__init__(ID, type_graph, name, Elements, root_element, Edges, Restrictions)


	def __hash__(self):
		return hash(arg for arg in self.Args) ^ hash(self.root.name) ^ hash(self.root.truth)

	def __eq__(self, other):
		if not isinstance(other, ElementGraph):
			return False
		if self.root.name == other.root.name and self.root.truth == other.root.truth:
			if self.Args == other.Args:
				return True
		return False

	def isConsistent(self, other):
		if isinstance(other, ElementGraph):
			return self.isConsistentSubgraph(other)
		if isinstance(other, Literal):
			return self.root.isConsistent(other)

	def numArgs(self):
		if not hasattr(self, 'Args'):
			self.updateArgs()
		return len({arg for arg in self.Args if not arg.name is None})

	def __repr__(self):
		#self.updateArgs()
		args = str([arg.__repr__() for arg in self.Args])
		#args = str([' {}-{} '.format(arg.name, arg.typ) for arg in self.Args
		#			if type(arg) is Argument else arg.__repr__()
		return '{}-{}{}'.format(self.root.truth, self.root.name, self.typ) + args

		
class PlanElementGraph(ElementGraph):
	def __init__(self, ID=None, type_graph=None, name=None, Elements=None, plan_elm=None, Edges=None,
				 Restrictions=None):
				
		if type_graph is None:
			type_graph = 'PlanElementGraph'
		if Elements is None:
			Elements = set()
		if Edges is None:
			Edges = set()
		if Restrictions is None:
			Restrictions = set()
		
		self.OrderingGraph = OrderingGraph()
		self.CausalLinkGraph = CausalLinkGraph()

		self.flaws = FlawLib()
		self.solved = False
		self.initial_dummy_step = None
		self.final_dummy_step = None

		if plan_elm is None:
			plan_elm = Element(ID=ID, typ=type_graph, name=name)
									
		super(PlanElementGraph,self).__init__(ID, type_graph, name, Elements, plan_elm, Edges, Restrictions)

	def __hash__(self):
		return hash(self.name) ^ hash(self.typ) ^ hash(self.ID)

	@classmethod
	def Actions_2_Plan(cls, Actions):
		# Used by Plannify

		elements = set().union(*[A.elements for A in Actions])
		edges = set().union(*[A.edges for A in Actions])
		Plan = cls(name='Action_2_Plan', Elements=elements, Edges=edges)
		for edge in Plan.edges:
			if edge.label == 'effect-of':
				elm = Plan.getElementById(edge.sink.ID)
				elm.replaced_ID = edge.sink.replaced_ID

		Plan.OrderingGraph = OrderingGraph()
		Plan.CausalLinkGraph = CausalLinkGraph()
		#Plan.Steps = [A.root for A in Actions]
		return Plan

	def UnifyActions(self, P, G):
		#Used by Plannify

		NG = G.deepcopy(replace_internals=True)
		for edge in list(NG.edges):

			if edge.sink.replaced_ID == -1:
				sink = copy.deepcopy(edge.sink)
				sink.replaced_ID = edge.sink.ID
				self.elements.add(sink)
			else:
				sink = P.getElmByRID(edge.sink.replaced_ID)
				if sink is None:
					sink = copy.deepcopy(edge.sink)
					self.elements.add(sink)

			source = P.getElmByRID(edge.source.replaced_ID)
			if source is None:
				source = copy.deepcopy(edge.source)
				self.elements.add(source)

			self.edges.add(Edge(source, sink, edge.label))

	@clock
	def Unify(self, other, GL):
		#self is story, other is ground subplan, which may have elements/IDs already in story.

		#only consider other steps if they aren't already in story!
		OSteps = other.Steps #[step for step in other.Steps if step not in self.Steps]
		SSteps = self.Steps

		Uni_Libs = [ReuseLib(i, s_add, SSteps) for i, s_add in enumerate(OSteps)]
		Uni_Worlds = itertools.product(*Uni_Libs)
		for ul  in Uni_Libs:
			if len(ul._cndts) > 1:
				pass

		New_Plans = set()
		for UW in Uni_Worlds:
			new_plan = self.deepcopy()
			for step in UW:
				if step not in SSteps:
					S_new = Action.subgraph(other, step).deepcopy()
					S_new.root.arg_name = step.stepnumber
					#move pieces
					new_plan.elements.update(S_new.elements)
					new_plan.edges.update(S_new.edges)
					#place in order
					new_plan.OrderingGraph.addEdge(new_plan.initial_dummy_step, S_new.root)
					new_plan.OrderingGraph.addEdge(S_new.root, new_plan.final_dummy_step)

			for ord in other.OrderingGraph.edges:
				new_plan.OrderingGraph.addEdge(UW[ord.source.position], UW[ord.sink.position])

			for link in other.CausalLinkGraph.edges:
				try:
					Source = Action.subgraph(new_plan, UW[link.source.position])
					#Source = Action.subgraph(new_plan, new_plan.getElmByRID(UW[link.source.position].replaced_ID))
				except:
					raise
				new_d = Source.getElmByRID(link.label.replaced_ID)
				if new_d is None:
					Sink = Action.subgraph(new_plan, UW[link.sink.position])
					new_d = Sink.getElmByRID(link.label.replaced_ID)
					if new_d is None:
						raise ValueError('here')
				new_plan.CausalLinkGraph.addEdge(UW[link.source.position], UW[link.sink.position], new_d)

			for step in UW:
				Step = Action.subgraph(new_plan, step)
				#Step = Action.subgraph(new_plan, new_plan.getElmByRID(step.replaced_ID))

				for pre in Step.preconditions:
					cndts = {edge for edge in new_plan.edges if isinstance(edge.source, Operator) and edge.sink == pre}
					if len(cndts) == 0:
						raise ValueError('wait, no edge for this preconditon? impossible!')
					if len(cndts) < 2:
						new_plan.flaws.insert(GL, new_plan, Flaw((step, pre), 'opf'))

			for step in UW:
				if step in OSteps:
					new_plan.flaws.addCndtsAndRisks(GL, UW[step.position])
			if new_plan.isInternallyConsistent():
				New_Plans.add(new_plan)

		return New_Plans

	def __lt__(self, other):
		return (self.cost + self.heuristic) < (other.cost + other.heuristic)

	def deepcopy(self):
		new_self = copy.deepcopy(self)
		new_self.ID = uid(21)
		return new_self

	def RemoveSubgraph(self, literal):
		elm = self.getElementById(literal.ID)
		link = None
		self.elements.remove(elm)

		for edge in list(self.edges):
			if edge.source == elm:
				self.edges.remove(edge)
			if link is None:
				if edge.sink == elm:
					link = edge
		return link

	def AddSubgraph(self, subgraph):
		self.elements.update(subgraph.elements)
		self.edges.update(subgraph.edges)


	def relaxedStep(self, GL, step, visited):

		cost = 0
		for pre in step.preconditions:
			v = self.relaxedPre(GL, pre, visited)
			cost += v

		return cost

	def relaxedPre(self, GL, pre, visited=None):
		if visited == None:
			visited = collections.defaultdict(int)

		antecedents = GL.id_dict[pre.replaced_ID]

		if len(antecedents) == 0:
			return 1000

		for ant in antecedents:
			if len(GL[ant].preconditions) == 0:
				visited[ant] = 1
				return 1

		if self.initial_dummy_step.stepnumber not in antecedents:
			least = 1000
			for ante in antecedents:

				if ante in visited.keys():
					v = visited[ante]
				else:
					visited[ante] = 1000
					v = self.relaxedStep(GL, GL[ante], visited)
					visited[ante] = v
				if v < least:
					least = v

			return least + 1
		return 0

	def calculateHeuristic(self, GL):
		value = 0

		for oc in self.flaws.flaws:
			_, pre = oc.flaw
			c = self.relaxedPre(GL, pre)
			oc.heuristic=c
			#print('flaw: {} , heuristic = {}'.format(oc,c))
			value += c

		return value

	@property
	def heuristic(self):

		"""
		Strategy: number of steps, dropping deletes, needed to fulfill all open conditions
		GList: story_GL.id_dict[pre.replaced_ID] for pre in step.preconditions
					while init.stepnumber not in story_GL.id_dict[pre.replaced_ID:

		@return:
		"""
		try:

			if self.name == 'story':
				return self.calculateHeuristic(GC.SGL)
			return self.calculateHeuristic(GC.DGL)
		except:
			return 0

		#return len(self.flaws) + k

	# + len(self.flaws.nonreusable)
		#return self.flaws.heuristic

	@property
	def cost(self):
		#if not hasattr(self, 'Steps'):
			#self.updatePlan()
		return len(self.Steps) - 2

	def isInternallyConsistent(self):
		return self.OrderingGraph.isInternallyConsistent() and self.CausalLinkGraph.isInternallyConsistent() and \
			   super(PlanElementGraph, self).isInternallyConsistent()

	@property
	def Steps(self):
		return [element for element in self.elements if type(element) is Operator]

	@property
	def Step_Graphs(self):
		return [Action.subgraph(self, step) for step in self.Steps]


	#@clock
	def detectThreatenedCausalLinks(self, GL):
		"""
		A threatened causal link flaw is a tuple <causal link edge, threatening step element>
			where if s --p--> t is a causal link edge and s_threat is the threatening step element,
				then there is no ordering path from t to s_threat,
				no ordering path from s_threat to s,
				there is an effect edge from s_threat to a literal false-p',
				and p' is consistent with p after flipping the truth attribute
		"""

		detectedThreatenedCausalLinks = set()
		nonThreats = self.CausalLinkGraph.nonThreats
		for causal_link in self.CausalLinkGraph.edges:
			for step in self.Steps:

				#defense 1
				if step in nonThreats[causal_link]:
					continue

				# defense 2-4 - First, ignore steps which either are the source and sink of causal link, or which cannot
				#  be ordered between them
				if step == causal_link.source or step == causal_link.sink:
					nonThreats[causal_link].add(step)
					continue
				if self.OrderingGraph.isPath(causal_link.sink, step):
					nonThreats[causal_link].add(step)
					continue
				if self.OrderingGraph.isPath(step, causal_link.source):
					nonThreats[causal_link].add(step)
					continue

				if step.stepnumber not in GL.threat_dict[causal_link.sink.stepnumber]:
					nonThreats[causal_link].add(step)
					continue

				detectedThreatenedCausalLinks.add(Flaw((step, causal_link), 'tclf'))
				#nonThreats[causal_link].add(step)

		return detectedThreatenedCausalLinks

	def __repr__(self):
		c = '\ncost {} + heuristic {}'.format(self.cost, self.heuristic)
		steps =  str([Action.subgraph(self, step) for step in self.Steps])
		orderings = self.OrderingGraph.__repr__()
		links = self.CausalLinkGraph.__repr__()
		return 'PLAN: ' + str(self.ID) + c + '\n*Steps: \n{' + steps + '}\n *Orderings:\n {' + orderings + '}\n ' '*CausalLinks:\n {' + links + '}'

class BiPlan:
	""" A container class for story and discourse plans, so they behave as a single plan. A tuple with functionality """
	weight = 1
	def __init__(self, Story, Disc):
		self.insert(Story)
		self.insert(Disc)

	def isInternallyConsistent(self):
		return self.S.isInternallyConsistent() and self.D.isInternallyConsistent()

	def deepcopy(self):
		new_self = copy.deepcopy(self)
		new_self.S.ID = uid(21)
		new_self.D.ID = uid(22)
		return new_self

	@property
	def heuristic(self):
		return self.S.heuristic + self.weight*self.D.heuristic

	@property
	def cost(self):
		return self.S.cost + self.weight*self.D.cost

	def __lt__(self, other):
		return (self.cost + self.heuristic) < (other.cost + other.heuristic)

	def num_flaws(self):
		return len(self.S.flaws) + len(self.D.flaws)

	def next_flaw(self):
		try:
			if len(self.D.flaws.statics) > 0:
				return 1, self.D.flaws.next()
			elif len(self.S.flaws.statics) > 0:
				return 0, self.S.flaws.next()
			elif len(self.S.flaws.inits) > 0:
				return 0, self.S.flaws.next()
			elif len(self.D.flaws) > 0:
				return 1, self.D.flaws.next()
			else:
				return 0, self.S.flaws.next()
		except:
			raise ValueError("shouldn't get here if no more flaws")

	def insert(self, kplan):
		if kplan.name == 'story':
			self.S = kplan
		else:
			self.D = kplan

	def __repr__(self):
		return self.S.__repr__() + self.D.__repr__()