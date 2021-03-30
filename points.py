import itertools
import json
import hashlib
from collections import defaultdict
from dataclasses import dataclass
from operator import attrgetter
from typing import List, Dict, Optional, Generator, Set, OrderedDict
from abc import ABC
from graphviz import Digraph


@dataclass
class PointType:
    points_id: str
    name: str
    starting_sum: int


@dataclass
class Condition(ABC):
    def run(self, choices):
        raise NotImplementedError


@dataclass
class TermCondition(Condition):
    data: dict

    def run(self, choices):
        return False


@dataclass
class RequiredCondition(Condition):
    object_id: str

    def run(self, choices):
        return self.object_id in choices

    def __repr__(self):
        return self.object_id


@dataclass
class IncompatibleCondition(Condition):
    object_id: str

    def run(self, choices):
        return self.object_id not in choices

    def __repr__(self):
        return f"!{self.object_id}"


@dataclass
class AndCondition(Condition):
    terms: List[Condition]

    def run(self, choices):
        return all(term.run(choices) for term in self.terms)

    def __repr__(self):
        return str.join(" && ", map(repr, self.terms))


@dataclass
class OrCondition(Condition):
    terms: List[Condition]

    def run(self, choices):
        return any(term.run(choices) for term in self.terms)

    def __repr__(self):
        return str.join(" || ", map(repr, self.terms))


@dataclass
class Score:
    points_id: str
    value: int
    requirements: Optional[Condition]


@dataclass
class RowObject:
    obj_id: str
    row_id: str
    title: str
    requirements: Optional[Condition]
    scores: List[Score]


@dataclass
class RowData:
    row_id: str
    title: str


@dataclass
class Vertex:
    inputs: Set[str]
    outputs: Set[str]


@dataclass
class Graph:
    rows: Dict[str, RowData]
    objects: Dict[str, RowObject]
    point_types: Dict[str, PointType]
    _vertices: Dict[str, Vertex] = None

    def objects_in_row(self, row_id):
        return sorted(filter(lambda item: item.row_id == row_id, self.objects.values()), key=attrgetter('obj_id'))

    @property
    def vertices(self):
        def build_vertices(objects: List[RowObject]):
            vertices = defaultdict(lambda: Vertex(set(), set()))

            def collect_condition_deps(cond: Optional[Condition]):
                if isinstance(cond, (AndCondition, OrCondition)):
                    for item in cond.terms:
                        yield from collect_condition_deps(item)
                elif isinstance(cond, (RequiredCondition, IncompatibleCondition)):
                    yield cond.object_id

            def collect_object_deps(obj: RowObject):
                yield from collect_condition_deps(obj.requirements)
                for score in obj.scores:
                    yield from collect_condition_deps(score.requirements)

            for obj in objects:
                vertices[obj.obj_id] = Vertex(set(), set())
            
            for oid, dep in ((obj.obj_id, dep) for obj in objects for dep in collect_object_deps(obj)):
                vertices[dep].outputs.add(oid)
                vertices[oid].inputs.add(dep)

            return vertices

        if self._vertices is None:
            self._vertices = build_vertices(self.objects.values())
        
        return self._vertices


@dataclass
class Component:
    component_id: str
    object_ids: Set[str]
    inputs: Set[str]
    outputs: Set[str]

    @property
    def object_id(self):
        return list(sorted(self.object_ids))[0]


@dataclass
class Stage:
    objects: OrderedDict[str, RowObject]


def build_graph(project_data):
    def build_requirement(data) -> Condition:
        if data['type'] == 'id' and data['required']:
            return RequiredCondition(data['reqId'])
        elif data['type'] == 'id' and not data['required']:
            return IncompatibleCondition(data['reqId'])
        elif data['type'] == 'or' and data['required']:
            return OrCondition([RequiredCondition(item['req'])
                                for item in data['orRequired'] if item['req']])
        else:
            return TermCondition(data)

    def build_requirements(data: list) -> Optional[Condition]:
        if len(data) == 0:
            return None
        elif len(data) == 1:
            return build_requirement(data[0])
        else:
            return AndCondition([build_requirement(item) for item in data])

    def build_score(data) -> Score:
        return Score(
            points_id=data['id'],
            value=int(data['value']),
            requirements=build_requirements(data['requireds'])
        )

    def build_object(object_data, row_id) -> RowObject:
        return RowObject(
            obj_id=object_data['id'],
            row_id=row_id,
            title=object_data['title'],
            requirements=build_requirements(object_data['requireds']),
            scores=[build_score(data) for data in object_data['scores']]
        )

    def build_row(row_data) -> RowData:
        return RowData(
            row_id=row_data['id'],
            title=row_data['title'],

        )

    return Graph(
        rows={row_data['id']: build_row(row_data)
              for row_data in project_data['rows']},
        objects={object_data['id']: build_object(object_data, row_data['id'])
                 for row_data in project_data['rows']
                 for object_data in row_data['objects']},
        point_types={data['id']: PointType(points_id=data['id'], name=data['name'], starting_sum=data['startingSum'])
                     for data in project_data['pointTypes']}
    )


def find_strongly_connected_components(graph: Graph):
    "Tarjan's Algorithm"
    last_group_index = 0
    stack = []
    index = {}
    lowlink = {}
    components = {}
    component_ownership = {}

    def strong_connect(key: str, vertex: Vertex):
        nonlocal last_group_index

        index[key] = last_group_index
        lowlink[key] = last_group_index
        last_group_index += 1
        stack.append(key)

        for child_key in vertex.outputs:
            if child_key not in lowlink:
                strong_connect(child_key, graph.vertices[child_key])
                lowlink[key] = min(lowlink[key], lowlink[child_key])
            elif child_key in stack:
                lowlink[key] = min(lowlink[key], index[child_key])

        if index[key] == lowlink[key]:
            object_ids = set()
            while stack[-1] != key:
                object_ids.add(stack.pop())
            object_ids.add(stack.pop())

            component_id = hashlib.sha256(str.join(';', object_ids).encode('utf-8')).hexdigest()[0:6]
            components[component_id] = Component(
                component_id=component_id,
                object_ids=object_ids,
                inputs=set(),
                outputs=set()
            )
            component_ownership.update({
                oid: component_id for oid in object_ids
            })

    for key, vertex in graph.vertices.items():
        if key not in index:
            strong_connect(key, vertex)

    # Build component connections
    for key, component in components.items():
        component.inputs = {
            component_ownership[vertex]
            for oid in component.object_ids
            for vertex in graph.vertices[oid].inputs
            if vertex not in component.object_ids
        }
        component.outputs = {
            component_ownership[vertex]
            for oid in component.object_ids
            for vertex in graph.vertices[oid].outputs
            if vertex not in component.object_ids
        }

    return components


def topological_sort(components: Dict[str, Component]):
    """Sort values subject to dependency constraints"""
    num_heads = defaultdict(int) # num arrows pointing in
    for key, component in components.items():
        num_heads[key] = len(component.inputs)

    ordered = [key for key in components.keys() if num_heads[key] == 0]
    for key in ordered:
        for child in components[key].outputs:
            num_heads[child] -= 1
            if num_heads[child] == 0:
                ordered.append(child)

    cycles = {key: (components[key], heads) for key, heads in num_heads.items() if key not in ordered}
    return ordered, cycles


def print_graph(graph: Graph):
    for row in graph.rows.values():
        print(f"[{row.row_id}] {row.title}")
        for obj in graph.objects_in_row(row.row_id):
            print(f"  - [{obj.obj_id}] {obj.title}")
            if len(obj.scores) > 0:
                scores_repr = [f"{graph.point_types[score.points_id].name}: {score.value} => {score.requirements}"
                               for score in obj.scores]
                print(f"    Scores: {str.join(', ', scores_repr)}")
            if obj.requirements:
                print(f"    Requirements: {repr(obj.requirements)}")


def print_cycles(cycles: Dict[str, Component], graph: Graph):
    all_cycles_set = set()

    def build_cycles(head, stack: list):
        if head in stack:
            return {str.join('>', sorted(stack)), }
        elif head in cycles:
            return set(child
                       for parent in cycles[head].outputs
                       for child in build_cycles(parent, [*stack, head]))
        else:
            return set()

    for head in cycles.keys():
        all_cycles_set = all_cycles_set | build_cycles(head, [])

    for cycle in all_cycles_set:
        cycle_ids = str.split(cycle, '>')
        cycle_objs = [graph.objects[oid] for oid in cycle_ids]
        cycle_str = [f"{graph.rows[obj.row_id].title} / {obj.title}"
                     for obj in cycle_objs]

        print(str.join("; ", cycle_str))


def render_graph(graph):
    dot = Digraph(comment='Dependencies')

    for key, vertex in graph.vertices.items():
        if len(vertex.inputs) == 0 and len(vertex.outputs) == 0:
            continue
        
        if obj := graph.objects.get(key):
            row_name = graph.rows[obj.row_id].title
            dot.node(obj.obj_id, f"{row_name} / {obj.title} [{obj.obj_id}]")
        else:
            dot.node(key, f"V-{key}")

    for key, vertex in graph.vertices.items():
        for parent in vertex.outputs:
            dot.edge(key, parent)

    dot = dot.unflatten(stagger=5)
    dot.render('graph.gv')


def render_components(graph: Graph, components: Dict[str, Component]):
    dot = Digraph(comment='Dependencies', graph_attr={'overlap':'vspc'})

    def add_node(dg, key):
        vertex = graph.vertices[key]
        if len(vertex.inputs) == 0 and len(vertex.outputs) == 0:
            return
        
        if obj := graph.objects.get(key):
            row_name = graph.rows[obj.row_id].title
            dot.node(obj.obj_id, f"{row_name} / {obj.title} [{obj.obj_id}]")
        else:
            dot.node(key, f"V-{key}")

    def unique_edges(component):
        edges = set()

        # External Edges
        for src, dst in ((src, dst) for src in component.object_ids for dst in graph.vertices[src].outputs):
            edges.add((src, dst))
        
        return edges

    for key, component in components.items():
        if len(component.object_ids) == 1:
            add_node(dot, component.object_id)
            for src, dst in unique_edges(component):
                dot.edge(src, dst)
        else:
            sg = Digraph(f'cluster_{key}')
            for key in component.object_ids:
                add_node(sg, key)

            for src, dst in unique_edges(component):
                sg.edge(src, dst)

            dot.subgraph(sg)

    dot = dot.unflatten(stagger=10)
    dot.render('components.gv')


def run_stages(stages, choices, points):
    def cond_match(requirements, choices):
        if requirements is not None:
            return requirements.run(choices)
        else:
            return True

    def run_stage(stage, points):
        for obj_id, row_obj in ((oid, obj) for oid, obj in stage.items() if oid in choices):
            if cond_match(row_obj.requirements, choices):
                print(f"Selected {row_obj.title} / {obj_id}")
                points = points | {
                    points_id: points.get(points_id, 0) - sum(score.value for score in scores if cond_match(score.requirements, choices))
                    for points_id, scores in itertools.groupby(sorted(row_obj.scores, key=attrgetter('points_id')), key=attrgetter('points_id'))
                }
            else:
                print(f"Invalid Selection {obj_id} !")

        return points
    
    for stage in stages:
        points = run_stage(stage, points)

    print(points)


if __name__ == '__main__':
    with open('viewer/project.json', mode='r') as fd:
        project = json.load(fd)

    graph = build_graph(project)
    # print_graph(graph)
    # render_graph(graph)

    components = find_strongly_connected_components(graph)
    # render_components(graph, components)
    
    sorted_deps, cycles = topological_sort(components)
    if len(cycles) > 0:
        print("Has a cycle")
        print(cycles)
    
    stages = [
        {n: graph.objects[n] for n in component.object_ids if n in graph.objects}
        for component in (components[n] for n in sorted_deps)
        if any(n in graph.objects for n in component.object_ids)
    ]
    
    print(f"{len(stages)} stages")
    
    choices = {"8mhz", "1psq", "deasy", "iwf0", "1y99", "g124", "i7bw", "kht1", "myd7", "puxg", "fbcq", "gl7t", "imhz", "0s6z", "sxhj",
               "hfao", "ar4o", "uh4g", "9mam", "4ech", "42jg", "87du", "w0ll", "eo3o", "akq3", "x88q", "pl4z", "xsyg", "6io0", "ui8c",
               "h8sf", "5dyo", "hheh", "okhr", "vczo", "l64d", "0yio", "08it", "z4p4", "bpuq", "hzoj", "prfi", "qokx", "346g", "0mr3",
               "ob4i", "9sto", "4jnj", "974r", "1irf", "q6x83", "4tfy", "1x0q"}
    
    run_stages(stages, choices, {pt.points_id: pt.starting_sum for pt in graph.point_types.values()})

