import heapq
import random
from collections import defaultdict


from utils import PropKB, Expr, new_disjunction, implies, associate
from typing import List, Dict, Union, Tuple
from utils import expr, to_cnf, conjuncts, disjuncts, remove_all

Literal = Union[str, expr]
Clause = List[Literal]
Model = Dict[Literal, bool]

from typing import List, Dict, Union, Tuple
from utils import expr, to_cnf, conjuncts, disjuncts, remove_all

Literal = Union[str, expr]
Clause = List[Literal]
Model = Dict[Literal, bool]


ids = ['214029415','213780455']
def dpll_satisfiable(s: expr) -> Model:
    """
    Check if a propositional formula is satisfiable using the DPLL algorithm.
    Args:
        s (expr): A propositional formula.
    Returns:
        Model: A model (dictionary of variable assignments) if satisfiable, otherwise an empty dictionary.
    """
    clauses = conjuncts(to_cnf(s))
    symbols = list({literal for clause in clauses for literal in disjuncts(clause)})
    result = dpll(clauses, symbols, {})
    return result if result else {}  # Return {} if unsatisfiable

def dpll(clauses: List[Clause], symbols: List[Literal], model: Model) -> Union[Model, None]:
    """
    Recursive DPLL algorithm for checking satisfiability.
    Args:
        clauses (List[Clause]): List of clauses in CNF.
        symbols (List[Literal]): List of all propositional symbols.
        model (Model): Current truth assignments.
    Returns:
        Union[Model, None]: A model if satisfiable, otherwise None.
    """
    # 1. Check if all clauses are satisfied
    if all(pl_true(clause, model) for clause in clauses):
        return model

    # 2. Check if any clause is unsatisfied
    if any(pl_true(clause, model) is False for clause in clauses):
        return None

    # 3. Find a pure symbol
    P, value = find_pure_symbol(symbols, clauses)
    if P is not None:
        return dpll(clauses, remove_all(P, symbols), extend(model, P, value))

    # 4. Find a unit clause
    P, value = find_unit_clause(clauses, model)
    if P is not None:
        return dpll(clauses, remove_all(P, symbols), extend(model, P, value))

    # 5. Choose a symbol and recurse
    P = symbols[0]
    rest = remove_all(P, symbols)
    return (dpll(clauses, rest, extend(model, P, True)) or
            dpll(clauses, rest, extend(model, P, False)))

def pl_true(clause: Clause, model: Model) -> Union[bool, None]:
    """
    Determine the truth value of a clause under the given model.
    Args:
        clause (Clause): A clause (disjunction of literals).
        model (Model): Current truth assignments.
    Returns:
        Union[bool, None]: True if satisfied, False if unsatisfied, None if undetermined.
    """
    unknown = False
    for literal in disjuncts(clause):
        sym, is_positive = inspect_literal(literal)
        if sym in model:
            if model[sym] == is_positive:
                return True
        else:
            unknown = True
    return None if unknown else False

def find_pure_symbol(symbols: List[Literal], clauses: List[Clause]) -> Tuple[Literal, bool]:
    """
    Find a pure symbol in the clauses.
    Args:
        symbols (List[Literal]): List of symbols.
        clauses (List[Clause]): List of clauses.
    Returns:
        Tuple[Literal, bool]: A pure symbol and its value, or (None, None) if none found.
    """
    counts = {}
    for clause in clauses:
        for literal in disjuncts(clause):
            sym, is_positive = inspect_literal(literal)
            if sym in counts:
                if counts[sym] != is_positive:  # Mixed polarity
                    counts[sym] = None
            else:
                counts[sym] = is_positive

    for sym, is_positive in counts.items():
        if is_positive is not None:
            return sym, is_positive

    return None, None

def find_unit_clause(clauses: List[Clause], model: Model) -> Tuple[Literal, bool]:
    """
    Find a unit clause in the clauses.
    Args:
        clauses (List[Clause]): List of clauses.
        model (Model): Current truth assignments.
    Returns:
        Tuple[Literal, bool]: A unit clause and its value, or (None, None) if none found.
    """
    for clause in clauses:
        unbound = []
        for literal in disjuncts(clause):
            sym, is_positive = inspect_literal(literal)
            if sym not in model:
                unbound.append((sym, is_positive))
            elif model[sym] == is_positive:
                break  # Clause already satisfied
        else:
            if len(unbound) == 1:  # Only one unbound literal
                return unbound[0]

    return None, None

def extend(model: Model, sym: Literal, value: bool) -> Model:
    """
    Extend the current model with a new symbol assignment.
    Args:
        model (Model): Current truth assignments.
        sym (Literal): Symbol to assign.
        value (bool): Value to assign.
    Returns:
        Model: Updated model.
    """
    return {**model, sym: value}

def inspect_literal(literal: Literal) -> Tuple[Literal, bool]:
    """
    Extract the symbol and polarity of a literal.
    Args:
        literal (Literal): A literal (e.g., 'A' or '~A').
    Returns:
        Tuple[Literal, bool]: The symbol and its polarity (True for positive, False for negative).
    """
    if literal.op == '~':
        return literal.args[0], False
    return literal, True


def Trap(x, y):
    return Expr('Trap', x, y)


def sulfur(x, y):
    return Expr('Sulfur', x, y)




def harry_location(x, y):
    return Expr('Loc', x, y)
class HarryPotterKB:
    def __init__(self, map_shape):
        """
        Initialize the Knowledge Base with map shape and forward chaining setup.
        """
        self.map_shape = map_shape
        self.facts = set()  # Known facts
        self.rules = []  # Rules as Horn clauses (premises -> conclusion)

        self.initialize_rules()

    def initialize_rules(self):
        """
        Add rules for sulfur and traps as Horn clauses.
        """
        for x in range(self.map_shape[0]):
            for y in range(self.map_shape[1]):
                neighbors = self.legal_grids((x, y))
                trap_neighbors = [Expr("Trap", nx, ny) for nx, ny in neighbors if neighbors[(nx, ny)]]

                # Rule 1: If sulfur, then at least one neighbor has a trap
                self.rules.append((set([Expr("Sulfur", x, y)]), trap_neighbors))

                # Rule 2: If no sulfur, then no neighbor has a trap
                self.rules.append((set([~Expr("Sulfur", x, y)]), [~Expr("Trap", nx, ny) for nx, ny in neighbors if neighbors[(nx, ny)]]))

    def legal_grids(self, location):
        """
        Returns valid neighbors for a given cell.
        """
        loc = {
            (location[0] + 1, location[1]): True,
            (location[0] - 1, location[1]): True,
            (location[0], location[1] + 1): True,
            (location[0], location[1] - 1): True,
        }
        for l in loc.keys():
            if l[0] < 0 or l[0] >= self.map_shape[0] or l[1] < 0 or l[1] >= self.map_shape[1]:
                loc[l] = False
        return loc

    def tell(self, fact):
        """
        Add a fact to the knowledge base and infer new facts.
        """
        if fact not in self.facts:
            self.facts.add(fact)
            self.infer_new_facts()

    def infer_new_facts(self):
        """
        Perform forward chaining to deduce new facts.
        """
        new_facts = set()
        for premises, conclusions in self.rules:
            if premises <= self.facts:  # All premises are satisfied
                for conclusion in conclusions:
                    if conclusion not in self.facts:
                        new_facts.add(conclusion)

        # Add newly inferred facts and recurse
        if new_facts:
            self.facts.update(new_facts)
            self.infer_new_facts()

    def ask_if_true(self, query):
        """
        Check if a query is true based on current knowledge.
        """
        return query in self.facts

    def new_ands(self,sen):
        t = sen[0]
        for i in range(1, len(sen)):
            t &= sen[i]
        return t

    def update_knowledge(self, observations, location):
        """
        Update KB with sulfur observations at a specific location to infer traps.
        - observations: List of tuples with observations, e.g., [("sulfur",), ("no_sulfur",)]
        - location: Tuple (x, y) indicating Harry's current position.
        """
        flag = False

        for obs in observations:
            if obs[0] == "sulfur":
                flag = True
                # Sulfur detected at the current location
                self.tell(sulfur(location[0], location[1]))
                neighbors = self.legal_grids(location)
                # If sulfur is present, at least one neighbor must have a trap

                trap_neighbors = [Trap(nx, ny) for nx, ny in neighbors if neighbors[(nx, ny)]]
                self.tell(implies(sulfur(location[0], location[1]), new_disjunction(trap_neighbors)))

        if flag == False:
            # No sulfur detected at the current location
            self.tell(~sulfur(location[0], location[1]))

            # If no sulfur, none of the neighbors can have a trap
            neighbors = self.legal_grids(location)
            no_trap_neighbors = [~Trap(nx, ny) for nx, ny in neighbors if neighbors[(nx, ny)]]
            self.tell(implies(~sulfur(location[0], location[1]), self.new_ands(no_trap_neighbors)))


class GringottsController:

    def __init__(self, map_shape, harry_loc, initial_observations):
        self.map_shape = map_shape
        self.harry_loc = harry_loc
        self.initial_observations = initial_observations
        self.kb = HarryPotterKB(map_shape)
        self.prev_moves = set()
        self.propositions = []
        self.remained_voults = []
        self.collected_voults = []
        self.prev_moves.add(self.harry_loc)
        for i in range(map_shape[0]):
            row = []
            for j in range(map_shape[1]):
                row.append({
                    "D": False,  # Is there a trap here?
                    "V": False,  # Is there a vault here?
                })
            self.propositions.append(row)
    def process_observations(self,observation):
        self.kb.update_knowledge(observation, self.harry_loc)
        for obs in observation:
            if obs[0] == 'vault':
                if obs[1] not in self.remained_voults and obs[1] not in self.collected_voults:
                    self.remained_voults.append(obs[1])
                    self.propositions[obs[1][0]][obs[1][1]]['V'] = True
            if obs[0] == 'dragon':
                self.propositions[obs[1][0]][obs[1][1]]['D'] = True

    def action_effect(self,action):
        if action[0] == 'move':
            self.harry_loc = action[1]
            self.prev_moves.add(self.harry_loc)
        if action[0] == 'collect':
            self.propositions[self.harry_loc[0]][self.harry_loc[1]]['V'] = False
            self.remained_voults.remove(self.harry_loc)
            self.collected_voults.append(self.harry_loc)
        if action[0] == 'destroy':
            # self.kb.retract(Trap(action[1][0], action[1][1]))
            self.kb.tell(~Trap(action[1][0], action[1][1]))
    def legal_grids(self,location):
        loc = {(location[0]+1,location[1]):True,(location[0]-1,location[1]):True,(location[0],location[1]+1):True,(location[0],location[1]-1):True}
        for l in loc.keys():
            if l[0] <0 or l[0] >= self.map_shape[0] or l[1] <0 or l[1] >= self.map_shape[1]:
                loc[l] = False
        return loc

    def legal_actions(self):
        actions = []
        if self.propositions[self.harry_loc[0]][self.harry_loc[1]]['V'] is True :
            actions.append(('collect',))
        for k,v in self.legal_grids(self.harry_loc).items():
            if v:
                # print((k, self.kb.ask_if_true(~Trap(k[0], k[1]))))
                if self.kb.ask_if_true(~Trap(k[0], k[1])) is True and self.propositions[k[0]][k[1]]['D'] is False:
                    actions.append(('move', k))
                # print((k, self.kb.ask_if_true(~Trap(k[0], k[1]))))
                if self.kb.ask_if_true(~Trap(k[0], k[1])) is False and self.propositions[k[0]][k[1]]['D'] is False and k not in self.prev_moves:
                    actions.append(('destroy', k))
        actions.append(('wait',))
        return actions

    def not_grid_moves(self,actions):
        legal = []
        for a in actions:
            if a[0] == 'move':
                if a[1][0] not in [0,self.map_shape[0]-1] and a[1][1] not in [0,self.map_shape[1]-1] and a[1] not in self.prev_moves:
                    legal.append(a[1])
        return legal

    def not_grid_destroy(self,actions):
        legal = []
        for a in actions:
            if a[0] == 'destroy':
                if a[1][0] not in [0,self.map_shape[0]-1] and a[1][1] not in [0,self.map_shape[1]-1] and a[1] not in self.prev_moves:
                    legal.append(a[1])
        return legal

    # def get_next_action(self, observations):
    #     """
    #     Decide Harry's next action based on the current state and observations.
    #     Prioritize collecting vaults, moving to unexplored areas, and avoiding traps.
    #     """
    #     self.process_observations(observations)
    #     actions = self.legal_actions()
    #
    #     # Priority 1: Collect Vaults
    #     for action in actions:
    #         if action[0] == 'collect':
    #             self.action_effect(action)
    #             return action
    #
    #     # Helper Functions
    #     def score_move(cell):
    #         """Score for movement actions based on proximity to vaults and exploration."""
    #         score = 0
    #         if cell not in self.prev_moves:
    #             score += 5  # Encourage exploration
    #         for vault in self.remained_voults:
    #             score += 10 / (self.manhatten(cell, vault) + 1)  # Closer to vaults is better
    #         return score
    #
    #     def score_destroy(cell):
    #         """Score for destruction actions based on unexplored neighbors."""
    #         neighbors = self.legal_grids(cell)
    #         unexplored = sum(1 for n in neighbors if n not in self.prev_moves)
    #         return unexplored
    #
    #
    #
    #     # Priority 2: Move toward vaults or unexplored areas
    #     move_scores = [(score_move(a[1]), a) for a in actions if a[0] == 'move']
    #     if move_scores:
    #         best_move = max(move_scores, key=lambda x: x[0])[1]
    #         self.prev_moves.add(best_move[1])
    #         self.action_effect(best_move)
    #         return best_move
    #
    #     # Priority 3: Destroy obstacles
    #     destroy_scores = [(score_destroy(a[1]), a) for a in actions if a[0] == 'destroy']
    #     if destroy_scores:
    #         best_destroy = max(destroy_scores, key=lambda x: x[0])[1]
    #         self.prev_moves.add(best_destroy[1])
    #         self.action_effect(best_destroy)
    #         return best_destroy
    #
    #     # Priority 4: Explore unexplored areas (Fallback)
    #     unexplored_cells = [
    #         cell for cell in self.get_all_cells() if cell not in self.prev_moves
    #     ]
    #     if unexplored_cells:
    #         farthest_cell = max(unexplored_cells, key=lambda c: self.manhatten(self.harry_loc, c))
    #         possible_moves = [(a[1], a) for a in actions if a[0] == 'move']
    #         best_move = min(possible_moves, key=lambda m: self.manhatten(m[0], farthest_cell))[1]
    #         self.prev_moves.add(best_move[1])
    #         self.action_effect(best_move)
    #         return best_move
    #
    #     # Priority 5: Default to wait
    #     return ('wait',)
    #
    # def get_all_cells(self):
    #     """
    #     Generate all cell coordinates for the map.
    #     """
    #     rows = self.map_shape[0] # Number of rows in the map
    #     cols = self.map_shape[1] if rows > 0 else 0  # Number of columns
    #     return [(r, c) for r in range(rows) for c in range(cols)]

    def get_next_action(self, observations):
        """
        Decide Harry's next action based on the current state and observations.
        Prioritize collecting vaults, avoiding traps, and safely navigating.
        """
        # Process observations and update the knowledge base
        self.process_observations(observations)
        # print(self.kb.clauses)
        # print(self.remained_voults)

        # Get all legal actions
        actions = self.legal_actions()
        print(actions)

        # Priority 1: Collect vaults
        for action in actions:
            if action[0] == 'collect':
                self.action_effect(action)
                # self.remained_voults.remove((self.harry_loc[0], self.harry_loc[1]))
                print(action)
                return action

        # Priority 2: Move closer to the nearest vault
        if len(self.remained_voults) > 0:

            closest_vault = min(
                self.remained_voults,
                key=lambda v: self.manhatten(v, self.harry_loc)
            )
            if closest_vault in self.remained_voults:
                for k, v in self.legal_grids(closest_vault):
                    if v:
                        if ('destroy', k) in actions and k not in self.prev_moves:
                            # if self.propositions[action[1][0]][action[1][1]]['D'] is False:
                                action = ('destroy', k)
                                self.action_effect(action)
                                # self.destroyed_traps.add(closest_vault)
                                print(action)
                                return action

            moves = [(a[1], self.manhatten(a[1], closest_vault)) for a in actions if a[0] == 'move']
            if moves:
                best_move = min(moves, key=lambda m: m[1])[0]
                if best_move not in self.prev_moves:
                    # self.prev_moves.add(best_move)
                    action = ('move', best_move)
                    self.action_effect(action)
                    # print('1')
                    print(action)
                    return action

            for k,v in self.legal_grids(self.harry_loc).items():
                if v:
                    for a in actions:
                        if a[0] == 'move':
                            if a[1] in self.remained_voults and a[1] == k:
                                action = ('move', k)
                                self.action_effect(action)
                                print(action)
                                return action



            # Destroy traps blocking the closest vault
            # Priority 2: Move toward unexplored areas



        # Priority 5: Wait as the last resort
        # return ('wait',)
        # Priority 3: Explore safely
        not_grid_moves = self.not_grid_moves(actions)
        not_grid_destroy = self.not_grid_destroy(actions)
        other_moves = []
        other_destroy = []
        corner_moves = []
        not_visited_moves = []
        corner_destroy = []
        for a in actions:
            if a[0] == 'move' and a[1] not in not_grid_moves:
                if a[1] not in self.prev_moves:
                    not_visited_moves.append(a[1])
                    if a[1] in [(1,0),(0,1),(self.map_shape[0]-2,0),(self.map_shape[1]-1,1),(0,self.map_shape[1]-2),(1,self.map_shape[1]-1),(self.map_shape[0]-2,self.map_shape[1]-1),(self.map_shape[0]-1,self.map_shape[1]-2)]:
                        corner_moves.append(a[1])
                else:
                    other_moves.append(a[1])
            if a[0] == 'destroy' and a[1] not in not_grid_destroy and a[1] not in self.prev_moves:
                if a[1] in [(1, 0), (0, 1), (self.map_shape[0] - 2, 0), (self.map_shape[1] - 1, 1),
                            (0, self.map_shape[1] - 2), (1, self.map_shape[1] - 1),
                            (self.map_shape[0] - 2, self.map_shape[1] - 1),
                            (self.map_shape[0] - 1, self.map_shape[1] - 2)]:
                    corner_destroy.append(a[1])
                else:
                    other_destroy.append(a[1])
        if len(not_grid_moves) > 0:
            print(f'not grid moves: {not_grid_moves}')
            rand = random.choice(not_grid_moves)
            action = ('move', rand)
            self.action_effect(action)
            print(action)
            return action
        if len(not_grid_destroy) > 0:
            print(f'destroy grid moves: {not_grid_destroy}')
            rand = random.choice(not_grid_destroy)
            action = ('destroy', rand)

            self.action_effect(action)
            print(action)
            return action


        if len(not_visited_moves) > 0:
            rand = random.choice(not_visited_moves)
            action = ('move', rand)
            self.action_effect(action)
            print(action)
            return action




        if len(corner_destroy) > 0:
            rand = random.choice(corner_destroy)
            action = ('destroy', rand)
            self.action_effect(action)
            print(action)
            return action

        if len(corner_moves) > 0:
            rand = random.choice(corner_moves)
            action = ('move', rand)
            self.action_effect(action)
            print(action)
            return action








        if len(other_destroy) > 0:
            rand = random.choice(other_destroy)
            action = ('destroy', rand)
            self.action_effect(action)
            print(action)
            return action

        if len(other_moves) > 0:
            rand = random.choice(other_moves)
            action = ('move', rand)
            self.action_effect(action)
            print(action)
            return action








        # Priority 4: Destroy remaining traps

        # Default to the first available action
        return ('wait', )
        # Priority 3: Explore safely

    from collections import defaultdict
    import heapq

    # def get_next_action(self, observations):
    #     """
    #     Determine Harry's next action based on the current state and observations.
    #     Prioritize collecting vaults, navigating to the closest one, and exploring unvisited areas.
    #     """
    #     # Update internal state with current observations
    #     self.process_observations(observations)
    #     actions = self.legal_actions()
    #
    #     # Priority 1: Collect vaults if Harry is on a vault
    #     for action in actions:
    #         if action[0] == 'collect':
    #             self.action_effect(action)
    #             return action
    #
    #     # Priority 2: Move closer to the nearest vault
    #     if self.remained_voults:
    #         closest_vault = min(
    #             self.remained_voults,
    #             key=lambda v: self.manhatten(v, self.harry_loc)
    #         )
    #         possible_moves = [
    #             (a[1], self.manhatten(a[1], closest_vault))
    #             for a in actions if a[0] == 'move'
    #         ]
    #         if possible_moves:
    #             best_move = min(possible_moves, key=lambda x: x[1])[0]
    #             if best_move not in self.prev_moves:
    #                 self.prev_moves.add(best_move)
    #                 self.action_effect(('move', best_move))
    #                 return ('move', best_move)
    #
    #     # Priority 3: Destroy obstacles blocking paths to vaults
    #     for action in actions:
    #         if action[0] == 'destroy' and action[1] not in self.prev_moves:
    #             self.action_effect(action)
    #             return action
    #
    #     # Priority 4: Explore unvisited areas
    #     def unexplored_score(cell):
    #         return max(self.manhatten(cell, move) for move in self.prev_moves) if self.prev_moves else 0
    #
    #     unexplored_moves = [
    #         (unexplored_score(a[1]), a)
    #         for a in actions if a[0] == 'move' and a[1] not in self.prev_moves
    #     ]
    #     if unexplored_moves:
    #         _, best_action = max(unexplored_moves, key=lambda x: x[0])
    #         self.prev_moves.add(best_action[1])
    #         self.action_effect(best_action)
    #         return best_action
    #
    #     # Priority 5: Destroy remaining traps or obstacles
    #     for action in actions:
    #         if action[0] == 'destroy':
    #             self.action_effect(action)
    #             return action
    #
    #     # Default to waiting if no valid actions are available
    #     return ('wait',)

    def manhatten(self,point1,point2):
        return abs(point1[0]-point2[0]) + abs(point1[1] - point2[1])
