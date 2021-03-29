import itertools
import json
from collections import defaultdict
from dataclasses import dataclass
from operator import attrgetter
from typing import List, Dict, Optional, Generator

from graphviz import Digraph


@dataclass
class PointType:
    points_id: str
    name: str
    starting_sum: int


@dataclass
class Condition:
    pass


@dataclass
class TermCondition(Condition):
    data: dict


@dataclass
class RequiredCondition(Condition):
    object_id: str

    def __repr__(self):
        return self.object_id


@dataclass
class IncompatibleCondition(Condition):
    object_id: str

    def __repr__(self):
        return f"!{self.object_id}"


@dataclass
class AndCondition(Condition):
    terms: List[Condition]

    def __repr__(self):
        return str.join(" && ", map(repr, self.terms))


@dataclass
class OrCondition(Condition):
    terms: List[Condition]

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
class Graph:
    rows: Dict[str, RowData]
    objects: Dict[str, RowObject]
    point_types: Dict[str, PointType]

    def objects_in_row(self, row_id):
        return sorted(filter(lambda item: item.row_id == row_id, self.objects.values()), key=attrgetter('obj_id'))


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
            value=data['value'],
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


def find_links(graph: Graph):
    children = defaultdict(list)
    parents = defaultdict(list)

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

    for obj in graph.objects.values():
        for dep in collect_object_deps(obj):
            children[dep].append(obj.obj_id)
            parents[obj.obj_id].append(dep)

    return children, parents


def find_strongly_connected_components(childen, parents, graph: Graph):
    last_group_index = 0
    stack = []
    index = {}
    lowlink = {}
    components = []

    def strong_connect(vertex):
        """
        function strongconnect(v)
            // Set the depth index for v to the smallest unused index
            v.index := index
            v.lowlink := index
            index := index + 1
            S.push(v)
            v.onStack := true

            // Consider successors of v
            for each (v, w) in E do
                if w.index is undefined then
                    // Successor w has not yet been visited; recurse on it
                    strongconnect(w)
                    v.lowlink := min(v.lowlink, w.lowlink)
                else if w.onStack then
                    // Successor w is in stack S and hence in the current SCC
                    // If w is not on stack, then (v, w) is an edge pointing to an SCC already found and must be ignored
                    // Note: The next line may look odd - but is correct.
                    // It says w.index not w.lowlink; that is deliberate and from the original paper
                    v.lowlink := min(v.lowlink, w.index)
                end if
            end for

            // If v is a root node, pop the stack and generate an SCC
            if v.lowlink = v.index then
                start a new strongly connected component
                repeat
                    w := S.pop()
                    w.onStack := false
                    add w to current strongly connected component
                while w ≠ v
                output the current strongly connected component
            end if
        end function
        """
        nonlocal last_group_index

        index[vertex] = last_group_index
        lowlink[vertex] = last_group_index
        last_group_index += 1
        stack.append(vertex)

        for child in childen[vertex]:
            if child not in lowlink:
                strong_connect(child)
                lowlink[vertex] = min(lowlink[vertex], lowlink[child])
            elif child in stack:
                lowlink[vertex] = min(lowlink[vertex], index[child])

        if index[vertex] == lowlink[vertex]:
            component = []
            while stack[-1] != vertex:
                component.append(stack.pop())
            component.append(stack.pop())
            components.append(component)

    for vertex in graph.objects.keys():
        strong_connect(vertex)

    return components


def topological_sort(children: dict, parents: dict):
    """Sort values subject to dependency constraints"""
    num_heads = defaultdict(int)  # num arrows pointing in
    for h, tt in parents.items():
        num_heads[h] = len(tt)

    ordered = [h for h in children if h not in num_heads]
    for h in ordered:
        for t in children[h]:
            num_heads[t] -= 1
            if not num_heads[t]:
                ordered.append(t)

    cyclic = {n: parents[n] for n, heads in num_heads.items() if heads > 0}
    return ordered, cyclic


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


def print_cycles(cycles: dict, graph: Graph):
    all_cycles_set = set()

    def build_cycles(head, stack: list):
        if head in stack:
            return {str.join('>', sorted(stack)), }
        elif head in cycles:
            return set(child
                       for parent in cycles[head]
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


def render_graph(children, parents, graph):
    dot = Digraph(comment='Dependencies')

    for obj in graph.objects.values():
        if len(children[obj.obj_id]) == 0 and len(parents[obj.obj_id]) == 0:
            continue
        row_name = graph.rows[obj.row_id].title
        dot.node(obj.obj_id, f"{row_name} / {obj.title} [{obj.obj_id}]")

    for child, obj_parents in children.items():
        for parent in obj_parents:
            dot.edge(child, parent)

    dot.render('graph.gv')


if __name__ == '__main__':
    with open('project.json', mode='r') as fd:
        project = json.load(fd)

    graph = build_graph(project)
    print_graph(graph)

    children, parents = find_links(graph)
    render_graph(children, parents, graph)

    components = find_strongly_connected_components(children, parents, graph)

    print(components)

    sorted_deps, cycles = topological_sort(children, parents)
    if len(cycles) > 0:
        print("Has a cycle")
        print_cycles(cycles, graph)
    else:
        print(sorted_deps)
