include "global_cardinality.mzn";

type Byte = 0..255;

int: max_pattern;
int: max_pattern_len;
array[int] of Byte: full_text;

%%% Definitions for the byte patterns that will form the compression
% Each pattern can be seen as slice of the full text, starting at an index and with a certain length.
enum Pattern = P(1..max_pattern);
array[Pattern] of var record(index_set(full_text): start, 0..max_pattern_len: len): slice;

%%% Definition of helper structure to ensure the full text is covered by the patterns
array[index_set(full_text)] of record(var Pattern: pat, var 1..max_pattern_len: index): cover;

% The byte covered matches the pattern that covers it
constraint forall(i in index_set(full_text)) (
    full_text[slice[cover[i].pat].start + cover[i].index - 1] = full_text[i]
);

% The cover indexes follow in sequence and until the end of a pattern
constraint forall(i in index_set(full_text)) (
    if i == min(index_set(full_text)) \/ cover[i-1].index = slice[cover[i-1].pat].len then
        cover[i].index = 1
    else
        cover[i].pat = cover[i-1].pat /\ cover[i].index = cover[i-1].index + 1
    endif
);
constraint cover[max(index_set(full_text))].index = slice[cover[max(index_set(full_text))].pat].len;

%%% Definition of the prefix codes that will depict each pattern
enum CodeTree = Internal(1..max_pattern-1) ++ Leaf(Pattern);
CodeTree: Root = Internal(1);
set of CodeTree: NonLeafNodes = Internal(1)..Internal(max_pattern-1);
set of CodeTree: NonRootNodes = Internal(2)..Leaf(max(Pattern));

% Parent of each node
array[NonRootNodes] of var opt NonLeafNodes: parent;
constraint forall(n in NonRootNodes) (parent[n] <= used_nodes);
constraint forall(p in Pattern) (occurs(parent[Leaf(p)]) <-> slice[p].len > 0);

% Nodes after this are unused
var NonLeafNodes: used_nodes;

% Number of times this node is a parent
array[NonLeafNodes] of var {0, 2}: parent_count;
constraint global_cardinality(
  parent,
  [n: n | n in NonLeafNodes],
  parent_count
);

% Cost of a node is the one more than the cost of its parent
array[CodeTree] of var 0..max_pattern: cost;
constraint cost[Root] = 0;
constraint forall(n in NonRootNodes) (cost[n] = ((cost[parent[n]] ~+ 1) default 0));

% Number of times a pattern is used
array[Pattern] of var int: uses = [p: count(c in cover) (c = (pat: p, index: 1)) | p in Pattern];

%%% Objective: Minimize the size of the encoding
var int: objective = sum (p in Pattern) (slice[p].len * 8 + cost[Leaf(p)] * (uses[p] + 1));
solve :: seq_search([
  int_search([used_nodes], input_order, indomain_min),
  int_search(
    [if i = 1 then s.start else s.len endif | s in slice, i in 1..2],
    first_fail,
    indomain_min
  ),
  int_search(parent, first_fail, indomain_min)
]) minimize objective;
