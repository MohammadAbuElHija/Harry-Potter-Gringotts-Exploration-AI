# Magical Vault Finder: AI Exploration System

## Key Features

### Knowledge Base (KB)
- Built on propositional logic to store facts and infer new knowledge.
- Observations like sulfur presence, vault locations, and traps are used to update the KB.
- Implements forward chaining, a rule-based reasoning algorithm, to deduce new facts from known observations.

### Observation Handling
- **Sulfur Detection**: If sulfur is detected at Harry's location, traps are inferred in the neighboring cells.
- **Vault Discovery**: Vaults are identified and tracked systematically.
- **No Sulfur**: If no sulfur is observed, the absence of traps in neighboring cells is inferred.

### Harry's Decision Logic
- **Legal Actions**: Determines valid actions (collect, move, destroy, wait) based on KB facts.
- **Action Prioritization**:
  - **Collect**: Prioritizes collecting a vault if present.
  - **Move**: Moves towards the nearest vault or unexplored areas.
  - **Destroy**: Destroys traps blocking progress.
  - **Explore**: Prioritizes unvisited cells and map corners.

### Exploration Strategy
- The map is split into quadrants for systematic exploration.
- Tracks visited cells to avoid redundant moves.
- Uses the Manhattan distance heuristic for movement decisions.

### Rule-Based Inference
- Rules like “If sulfur, then at least one neighboring cell contains a trap” guide decision-making.
- Forward chaining ensures new observations dynamically update Harry's strategy.

## How It Works

### Observation Processing
- Harry observes clues like sulfur or traps in his surroundings.
- Observations update the KB, inferring traps or safe paths using forward chaining.

### Action Determination
- Based on the KB, Harry selects actions by prioritizing vault collection, safe navigation, or trap destruction.

### Systematic Exploration
- Quadrants and unexplored areas are prioritized to ensure comprehensive map coverage.

This AI intelligently combines observation-based reasoning with heuristic-driven exploration to efficiently guide Harry to the magical vaults.

