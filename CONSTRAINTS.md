# Crusher Constraint Reference

This document provides comprehensive documentation for the global constraints available in Crusher.

## Global Constraints

### Cumulative Constraint

**Function**: `cumulative(originPositions, durations, heights, limit)`

**Definition**: Resource-constrained scheduling constraint that ensures at each point in time, the total resource consumption of overlapping tasks does not exceed a given capacity limit.

**Mathematical Form**: `∀t ∈ Time : Σ(tasks i where origin[i] ≤ t < origin[i] + duration[i]) height[i] ≤ limit`

**Parameters**:
- `originPositions`: Variable positions representing task start times
- `durations`: Duration of each task (constant values)
- `heights`: Resource consumption/demand of each task (constant values)
- `limit`: Maximum resource capacity available

**Usage Examples**:
```nim
# Project scheduling: 5 tasks with resource constraints
let durations = @[3, 9, 10, 6, 2]
let heights = @[1, 2, 1, 1, 3]
let limit = 8

var sys = initConstraintSystem[int]()
var origins = sys.newConstrainedSequence(5)
origins.setDomain(toSeq(1..20))

sys.addConstraint(cumulative[int]([0,1,2,3,4], durations, heights, limit))
sys.resolve()

# Machine scheduling with limited capacity
let machineDurations = @[4, 3, 5, 2]
let machineLoads = @[3, 2, 4, 1]
let machineCapacity = 6

sys.addConstraint(cumulative[int](taskPositions, machineDurations, machineLoads, machineCapacity))

# Expression-based origins (e.g., x[i] + offset[i])
var originExprs: seq[AlgebraicExpression[int]] = @[]
for i in 0..< n:
    originExprs.add(x[i] + offsets[i])
sys.addConstraint(cumulative[int](originExprs, durations, heights, limit))
```

**Applications**:
- **Project Scheduling**: Tasks competing for shared resources (workers, machines, tools)
- **Manufacturing**: Production scheduling with machine capacity constraints
- **Computing**: Job scheduling with CPU/memory/bandwidth limits
- **Logistics**: Vehicle routing with capacity constraints over time
- **Energy Management**: Power consumption scheduling within grid capacity
- **Workforce Planning**: Staff allocation with headcount limits per time period

**Violation Cost**: Sum of resource overloads across all time points
- For each time `t` where demand > limit: `cost += (demand - limit)`
- Encourages solutions that minimize resource conflicts and overutilization

**Performance**:
- Efficient incremental updates via event-based timeline tracking
- O(k) move evaluation where k = number of affected time points
- Optimized for both position-based and expression-based evaluations
- Integrated with Crusher's tabu search and parallel optimization

**Key Features**:
- **Event-based tracking**: Maintains resource profile only for active time points
- **Incremental updates**: Efficiently recalculates only affected portions of timeline
- **Expression support**: Origins can be algebraic expressions (e.g., `x[i] + delay`)
- **Auto-optimization**: Automatically uses faster position-based mode when possible

---

### Multiknapsack Constraint

**Function**: `multiknapsack(positions, weights, capacities)`

**Definition**: Ensures that for each value `v` in the domain, the total weight of items assigned to value `v` does not exceed the capacity for that value.

**Mathematical Form**: `∀v ∈ Values : Σ(i where x[i] = v) weights[i] ≤ capacity[v]`

**Parameters**:
- `positions`: Array of variable positions/indices
- `weights`: Weight of each position (same length as positions)  
- `capacities`: Array of `(value, capacity)` pairs defining capacity limits

**Usage Examples**:
```nim
# Bin packing: 3 bins with different capacities
let constraint = multiknapsack[int]([0,1,2,3,4], [2,3,1,4,2], [(1,5), (2,7), (3,4)])

# Resource allocation: servers with different processing capacities
let constraint = multiknapsack[int](serverPositions, taskWeights, serverCapacities)

# Load balancing example
var sys = initConstraintSystem[int]()
var tasks = sys.newConstrainedSequence(5)
tasks.setDomain(toSeq(1..3))  # 3 servers

# Task weights and server capacities
let weights = [10, 15, 8, 12, 20]  # CPU requirements
let serverCaps = [(1, 30), (2, 35), (3, 25)]  # Server capacities

let loadBalancer = multiknapsack[int]([0,1,2,3,4], weights, serverCaps)
sys.addConstraint(loadBalancer)
```

**Applications**:
- **Bin Packing**: Assigning items to bins without exceeding bin capacity
- **Resource Allocation**: Distributing tasks to resources (servers, machines) with capacity limits
- **Load Balancing**: Ensuring no resource is overloaded beyond its capacity
- **Scheduling**: Assigning jobs to time slots with processing capacity constraints
- **Logistics**: Vehicle routing with weight/volume capacity constraints

**Violation Cost**: Sum of over-capacity amounts across all values
- If a value's total load exceeds its capacity, cost += (load - capacity)
- Well-balanced loads across capacities minimize total cost

**Performance**: 
- Efficient incremental updates via `moveDelta()`
- O(1) cost calculation for position changes
- Integrated with Crusher's tabu search algorithms

---

### Sequence Constraint

**Function**: `sequence(positions, minInSet, maxInSet, windowSize, targetSet)`

**Definition**: Ensures that among any `windowSize` consecutive variables in the sequence, at least `minInSet` and at most `maxInSet` variables take their values from the target set `S`.

**Mathematical Form**: `∀i ∈ [0, n-windowSize] : minInSet ≤ |{j ∈ [i, i+windowSize-1] : x[j] ∈ S}| ≤ maxInSet`

**Parameters**:
- `positions`: Array of variable positions forming the sequence
- `minInSet`: Minimum number of variables that must be in target set per window
- `maxInSet`: Maximum number of variables that can be in target set per window
- `windowSize`: Size of the consecutive window to check
- `targetSet`: Set of values to count within each window

**Usage Examples**:
```nim
# Work schedule: In any 7 consecutive days, at least 2 must be rest days
let constraint = sequence[int]([0,1,2,3,4,5,6], 2, 7, 7, [REST_DAY])

# Equipment usage: No more than 3 consecutive slots can use high-power mode
let constraint = sequence[int](timeSlots, 0, 3, 4, [HIGH_POWER])

# Quality control: In every 5 consecutive products, exactly 1 must be inspected
let constraint = sequence[int](products, 1, 1, 5, [INSPECT])

# Nurse scheduling example
var sys = initConstraintSystem[int]()
var schedule = sys.newConstrainedSequence(14)  # 2-week schedule
schedule.setDomain([WORK, REST, NIGHT])

# In any 7 consecutive days, at least 2 must be rest days
let restPattern = sequence[int]([0,1,2,3,4,5,6,7,8,9,10,11,12,13], 2, 7, 7, [REST])
sys.addConstraint(restPattern)

# No more than 3 consecutive night shifts
let nightLimit = sequence[int]([0,1,2,3,4,5,6,7,8,9,10,11,12,13], 0, 3, 4, [NIGHT])
sys.addConstraint(nightLimit)
```

**Applications**:
- **Work Scheduling**: Enforcing rest periods, break patterns, shift regulations
- **Resource Management**: Limiting consecutive usage of expensive resources
- **Quality Control**: Ensuring regular inspection/testing patterns
- **Manufacturing**: Controlling machine setup changes and maintenance windows
- **Network Traffic**: Managing burst patterns and rate limiting
- **Healthcare**: Patient care scheduling with mandatory rest periods
- **Education**: Course scheduling with workload distribution requirements

**Violation Cost**: Sum of violations across all windows
- For each window: cost += max(0, minInSet - count) + max(0, count - maxInSet)
- Ensures all consecutive windows satisfy the count requirements

**Performance**:
- Efficient window-based evaluation
- Incremental updates via `moveDelta()` for affected windows only
- Optimized for both small and large window sizes

---

## Cardinality Constraints

### AtLeast Constraint

**Function**: `atLeast(positions, targetValue, minOccurrences)`

**Definition**: Ensures that `targetValue` appears at least `minOccurrences` times in the specified positions.

**Mathematical Form**: `|{i ∈ positions : x[i] = targetValue}| ≥ minOccurrences`

**Parameters**:
- `positions`: Array of variable positions to check
- `targetValue`: The value to count occurrences of
- `minOccurrences`: Minimum required occurrences

**Usage Examples**:
```nim
# At least 3 occurrences of value 1 in positions 0-4
let constraint = atLeast[int]([0,1,2,3,4], 1, 3)

# Resource allocation: At least 2 tasks must be assigned to server 1
let serverConstraint = atLeast[int](taskPositions, SERVER1, 2)

# Scheduling: At least 2 days must be rest days
let restConstraint = atLeast[int](weekDays, REST_DAY, 2)
```

**Applications**:
- **Resource Planning**: Ensuring minimum resource utilization
- **Workforce Scheduling**: Minimum staffing requirements
- **Quality Assurance**: Minimum number of inspections/tests
- **Load Balancing**: Minimum tasks per server/processor

**Violation Cost**: `max(0, minOccurrences - actualCount)`
- Cost increases linearly with shortage
- Zero cost when requirement is met or exceeded

---

### AtMost Constraint

**Function**: `atMost(positions, targetValue, maxOccurrences)`

**Definition**: Ensures that `targetValue` appears at most `maxOccurrences` times in the specified positions.

**Mathematical Form**: `|{i ∈ positions : x[i] = targetValue}| ≤ maxOccurrences`

**Parameters**:
- `positions`: Array of variable positions to check
- `targetValue`: The value to limit occurrences of
- `maxOccurrences`: Maximum allowed occurrences

**Usage Examples**:
```nim
# At most 2 occurrences of value 5 in positions 0-4
let constraint = atMost[int]([0,1,2,3,4], 5, 2)

# Capacity management: At most 3 high-priority tasks
let priorityLimit = atMost[int](taskPositions, HIGH_PRIORITY, 3)

# Work regulations: At most 5 night shifts per period
let nightLimit = atMost[int](shiftSchedule, NIGHT_SHIFT, 5)
```

**Applications**:
- **Capacity Management**: Preventing resource overload
- **Regulatory Compliance**: Maximum working hours, overtime limits
- **Risk Management**: Limiting exposure to high-risk activities
- **Budget Constraints**: Maximum expensive operations

**Violation Cost**: `max(0, actualCount - maxOccurrences)`
- Cost increases linearly with excess
- Zero cost when within limit

---

### Global Cardinality Constraint

**Function**: `globalCardinality(positions, values, counts)` / `globalCardinalityBounded(positions, values, lowerBounds, upperBounds)`

**Definition**: Ensures specific occurrence counts for multiple values simultaneously. Supports both exact counts and bounded counts.

**Mathematical Form**: 
- Exact: `∀v ∈ values : |{i ∈ positions : x[i] = v}| = count[v]`
- Bounded: `∀v ∈ values : lowerBound[v] ≤ |{i ∈ positions : x[i] = v}| ≤ upperBound[v]`

**Parameters**:
- `positions`: Array of variable positions
- `values`: Array of values to constrain (cover set)
- `counts`: Exact target counts for each value (exact version)
- `lowerBounds/upperBounds`: Count ranges for each value (bounded version)

**Usage Examples**:
```nim
# Exact counts: exactly 2 ones, 3 twos, and 1 three
let exact = globalCardinality[int]([0,1,2,3,4,5], [1,2,3], [2,3,1])

# Bounded counts: 1-3 type A, 2-4 type B, 0-2 type C
let bounded = globalCardinalityBounded[int](
    [0,1,2,3,4,5,6,7,8], 
    [TYPE_A, TYPE_B, TYPE_C], 
    [1, 2, 0],  # lower bounds
    [3, 4, 2]   # upper bounds
)

# Team composition: specific role distribution
let teamStructure = globalCardinality[int](
    teamPositions, 
    [MANAGER, DEVELOPER, TESTER], 
    [1, 4, 2]
)
```

**Applications**:
- **Team Composition**: Specific role distributions in teams
- **Resource Allocation**: Balanced distribution across categories
- **Manufacturing**: Product mix with specific ratios
- **Exam Scheduling**: Balanced distribution of exam types
- **Workforce Planning**: Skill distribution requirements

**Violation Cost**: Sum of deviations from target counts/bounds
- Exact: `Σ |actualCount[v] - targetCount[v]|`
- Bounded: `Σ (max(0, lowerBound[v] - actualCount[v]) + max(0, actualCount[v] - upperBound[v]))`

---

## Ordering Constraints

### Increasing Constraint

**Function**: `increasing(positions)`

**Definition**: Ensures variables are in non-decreasing order: `x[i] ≤ x[i+1]` for consecutive positions.

**Mathematical Form**: `∀i ∈ [0, n-2] : x[positions[i]] ≤ x[positions[i+1]]`

**Usage Examples**:
```nim
# Variables must be in non-decreasing order
let constraint = increasing[int]([0,1,2,3,4])

# Task scheduling: start times must be non-decreasing
let scheduleOrder = increasing[int](taskStartTimes)

# Resource allocation: priority levels in ascending order
let priorityOrder = increasing[int](priorityPositions)
```

**Applications**:
- **Task Scheduling**: Ensuring chronological order
- **Priority Systems**: Maintaining priority hierarchies
- **Data Processing**: Sorted sequence requirements
- **Resource Allocation**: Ordered assignment patterns

---

### Strictly Increasing Constraint

**Function**: `strictlyIncreasing(positions)`

**Definition**: Ensures variables are in strictly increasing order: `x[i] < x[i+1]` for consecutive positions.

**Mathematical Form**: `∀i ∈ [0, n-2] : x[positions[i]] < x[positions[i+1]]`

**Usage Examples**:
```nim
# Variables must be in strictly increasing order
let constraint = strictlyIncreasing[int]([0,1,2,3,4])

# Unique timestamps: each event must occur after the previous
let eventOrder = strictlyIncreasing[int](eventTimes)

# Performance benchmarks: each level must be higher than previous
let benchmarkLevels = strictlyIncreasing[int](performanceMetrics)
```

**Applications**:
- **Event Sequencing**: Ensuring unique timestamps
- **Performance Metrics**: Strictly improving benchmarks
- **Game Levels**: Difficulty progression
- **Version Control**: Monotonically increasing version numbers

---

### Decreasing Constraint

**Function**: `decreasing(positions)`

**Definition**: Ensures variables are in non-increasing order: `x[i] ≥ x[i+1]` for consecutive positions.

**Mathematical Form**: `∀i ∈ [0, n-2] : x[positions[i]] ≥ x[positions[i+1]]`

**Usage Examples**:
```nim
# Variables must be in non-increasing order
let constraint = decreasing[int]([0,1,2,3,4])

# Resource depletion: remaining capacity decreases over time
let capacityOrder = decreasing[int](capacityLevels)

# Budget allocation: higher priority items get more budget
let budgetOrder = decreasing[int](budgetAllocations)
```

**Applications**:
- **Resource Management**: Modeling depletion patterns
- **Priority-Based Allocation**: Higher priorities get more resources
- **Performance Degradation**: Modeling system decline
- **Cost Optimization**: Decreasing cost structures

---

### Strictly Decreasing Constraint

**Function**: `strictlyDecreasing(positions)`

**Definition**: Ensures variables are in strictly decreasing order: `x[i] > x[i+1]` for consecutive positions.

**Mathematical Form**: `∀i ∈ [0, n-2] : x[positions[i]] > x[positions[i+1]]`

**Usage Examples**:
```nim
# Variables must be in strictly decreasing order
let constraint = strictlyDecreasing[int]([0,1,2,3,4])

# Tournament rankings: each position must be strictly higher rated
let rankingOrder = strictlyDecreasing[int](playerRankings)

# Temperature cooling: each measurement must be lower than previous
let coolingPattern = strictlyDecreasing[int](temperatureReadings)
```

**Applications**:
- **Ranking Systems**: Ensuring distinct ranks
- **Process Monitoring**: Strictly decreasing patterns
- **Quality Control**: Monotonic improvement requirements
- **Optimization**: Ensuring strict improvement

**Violation Cost** (All Ordering Constraints): Sum of ordering violations
- For each violated pair: cost += `|violation_amount|`
- Efficient incremental updates when positions change

---

## Other Global Constraints

### AllDifferent Constraint

**Function**: `allDifferent(positions)`

**Definition**: Ensures all variables in the specified positions take different values (no duplicates).

**Mathematical Form**: `∀i,j ∈ positions, i ≠ j : x[i] ≠ x[j]`

**Parameters**:
- `positions`: Array of variable positions that must have distinct values

**Usage Examples**:
```nim
# All variables must have different values
let constraint = allDifferent[int]([0,1,2,3,4])

# N-Queens: no two queens in same row
let rowConstraint = allDifferent[int](rowPositions)

# Resource assignment: each task gets a unique resource
let uniqueAssignment = allDifferent[int](taskResourcePairs)

# Scheduling: each time slot gets a unique activity
let scheduleConstraint = allDifferent[int](timeSlotActivities)
```

**Applications**:
- **N-Queens Problem**: Ensuring no conflicts
- **Resource Assignment**: Unique resource allocation
- **Scheduling**: Non-overlapping activities
- **Permutation Problems**: Generating unique arrangements
- **Graph Coloring**: Adjacent nodes get different colors
- **Sudoku**: Row/column/box uniqueness

**Violation Cost**: Sum of conflicts between duplicate values
- Cost increases with number of duplicate pairs
- Efficient tracking using value frequency counts

**Performance**: O(1) incremental updates using hash table counting

---

### Element Constraint

**Function**: `element(indexExpr, array, valueExpr)`

**Definition**: Enforces the indexing relationship `array[indexExpr] = valueExpr`, where the array can be constants, variables, or mixed.

**Mathematical Form**: `array[index] = value`

**Parameters**:
- `indexExpr`: Expression/variable representing the array index
- `array`: Array of constants, variables, or mixed elements
- `valueExpr`: Expression/variable that must equal the indexed array element

**Usage Examples**:
```nim
# Constant array indexing
let constantArray = [10, 20, 30, 40, 50]
let constraint1 = element[int](indexVar, constantArray, valueVar)

# Variable array indexing (array elements are variables)
let variableArray = @[var1, var2, var3, var4]
let constraint2 = element[int](indexVar, variableArray, valueVar)

# Configuration selection: select config based on mode
let configs = [CONFIG_A, CONFIG_B, CONFIG_C]
let configConstraint = element[int](modeSelector, configs, activeConfig)

# Lookup table: map input to output value
let lookupTable = [0, 1, 4, 9, 16, 25]  # squares
let squareConstraint = element[int](inputVar, lookupTable, outputVar)
```

**Applications**:
- **Lookup Tables**: Implementing function mappings
- **Configuration Selection**: Choose settings based on mode
- **Data Structure Modeling**: Array/list access patterns
- **Routing Problems**: Path selection from alternatives
- **Resource Mapping**: Dynamic resource assignment
- **State Machines**: State transition tables

**Constraint Variants**:
- **Constant Array**: `element(index, [1,2,3,4], value)` - Fixed lookup table
- **Variable Array**: `element(index, [var1,var2,var3], value)` - Array elements are variables
- **Mixed Array**: `element(index, [const1,var1,const2], value)` - Mixed constants and variables

**Violation Cost**: Binary (0 if satisfied, 1 if violated)
- Checks exact equality: `array[index] == value`
- Handles bounds checking automatically

**Performance**: Efficient evaluation with caching of array element values

---

## Constraint Composition

All constraints can be combined within a single `ConstraintSystem`:

```nim
var sys = initConstraintSystem[int]()
var variables = sys.newConstrainedSequence(10)
variables.setDomain(toSeq(1..5))

# Multiple constraint types working together
sys.addConstraint(allDifferent[int]([0,1,2,3,4]))
sys.addConstraint(sequence[int]([0,1,2,3,4,5,6,7,8,9], 2, 4, 5, [1,2]))
sys.addConstraint(multiknapsack[int]([5,6,7,8,9], [3,2,4,1,5], [(3,8), (4,10), (5,6)]))

sys.resolve()
```

---

## Performance Considerations

- **Incremental Updates**: All global constraints support efficient `moveDelta()` operations for tabu search
- **Expression vs Position-Based**: Position-based constraints are more efficient when possible
- **Constraint Ordering**: Place more restrictive constraints first for better pruning
- **Domain Reduction**: Smaller domains improve search performance

---

## Integration with Search

Crusher's global constraints are fully integrated with:
- **Tabu Search**: Efficient neighborhood exploration with constraint-aware move evaluation
- **Parallel Search**: Thread-safe constraint copying for parallel optimization
- **Heuristic Search**: Custom search strategies can leverage constraint violation costs
- **Constraint Propagation**: Domain reduction based on constraint analysis

For implementation details, see the source files in `src/constraints/`.