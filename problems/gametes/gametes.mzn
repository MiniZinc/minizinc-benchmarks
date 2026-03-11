% MIT License

% Copyright (c) 2023 Kelvin Davis

% Permission is hereby granted, free of charge, to any person obtaining a copy
% of this software and associated documentation files (the "Software"), to deal
% in the Software without restriction, including without limitation the rights
% to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
% copies of the Software, and to permit persons to whom the Software is
% furnished to do so, subject to the following conditions:

% The above copyright notice and this permission notice shall be included in all
% copies or substantial portions of the Software.

% THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
% IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
% FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
% AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
% LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
% OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
% SOFTWARE.

% Changes by the MiniZinc Challenge Organisers:
% - Add basic search annotation
% - Move some local variables to the top-level so that they could be added to the search strategy

include "globals.mzn";

int: nLoci;
int: nGametes;
set of int: NLoci = 1..nLoci;
set of int: NLociDiff = NLoci diff {1};
set of int: NGametes = 1..nGametes;
set of int: NGametesOpt = {0} union NGametes;
int: maxCrossovers;

int: nTreeCells;
set of int: NTreeCells = 1..nTreeCells;

enum NodeType = {Node, Leaf, Null};
array[NTreeCells] of var NodeType: treeType;
array[NTreeCells] of var NTreeCells union {0}: treeLeft;
array[NTreeCells] of var NTreeCells union {0}: treeRight;

% Tree structure
constraint increasing(treeType);
constraint forall (i in NTreeCells where treeType[i] == Node) (
  treeLeft[i] > i /\
  treeRight[i] > i /\
  treeType[treeLeft[i]] != Null /\
  treeType[treeRight[i]] != Null /\
  true
);
constraint forall (i in NTreeCells where treeType[i] != Node) (
  treeLeft[i] = 0 /\ treeRight[i] = 0
);

set of int: B = 0..1;
array[NGametes, NLoci] of B: gametes;
array[NTreeCells, NLoci] of var B: xs;

array[NTreeCells] of var NGametesOpt: index;
constraint forall (i in NTreeCells) (
  (treeType[i] = Leaf <-> index[i] > 0) /\
  (treeType[i] = Null <-> xs[i, NLoci] = [0 | _ in NLoci])
);
constraint all_different_except_0(index);
% constraint let {
%   array[NTreeCells] of var NGametesOpt: indexCummulative;
%   constraint indexCummulative[1] = index[1];
%   constraint forall (i in NTreeCells diff {1}) (
%     if index[i] > 0
%     then indexCummulative[i] = index[i]
%     else indexCummulative[i] = indexCummulative[i-1]
%     endif
%   );
%   constraint forall (i in NTreeCells diff {1}) (
%     if treeType[i] == Null
%     then indexCummulative[i] = indexCummulative[i-1]
%     else indexCummulative[i] = index[i]
%     endif
%   );
% } in increasing(indexCummulative);
constraint forall (i in NTreeCells where treeType[i] == Leaf) (
  forall (j in NLoci) (
    xs[i, j] = gametes[index[i], j]
  )
);


% First plant is the desired plant
constraint xs[1, NLoci] == [1 | _ in NLoci] /\ treeType[1] != Null;

% Each internal node and its child nodes (genetic parents in reality)
% must be related by crossing
array[NTreeCells, NLoci] of var 1..2: source;
array[NTreeCells, NLociDiff] of var 0..1: swap;
constraint forall (i in NTreeCells) (
  if treeType[i] = Node then
    crossedGamete(
      treeLeft[i],
      treeRight[i],
      i,
    )
  else
    forall (j in NLoci) (source[i, j] = 1) /\
    forall (j in NLociDiff) (swap[i, j] = 0)
  endif
);

predicate crossedGamete(
  var NTreeCells: igx,
  var NTreeCells: igy,
  NTreeCells: igz,
) = (
  let {
    constraint forall (j in NLoci diff {1}) (
      swap[igz,j] = 1 <-> source[igz,j-1] != source[igz,j]
    );
    constraint sum(swap[igz, ..]) <= maxCrossovers;
    % redundant constraint
    constraint count(swap[igz, ..], 1) <= maxCrossovers;
    % dominance
    %constraint forall (j in NLociDiff) (
    %  let {
    %    var B: a = xs[igx, j-1];
    %    var B: b = xs[igx, j];
    %    var B: c = xs[igy, j-1];
    %    var B: d = xs[igy, j];
    %    var B: e = xs[igz, j-1];
    %    var B: f = xs[igz, j];
    %  } in swap[j] = 1 <-> (
    %    b != d /\
    %    f = 1 /\
    %    [b, d][source[j]] = 1 /\
    %    [d, b][source[j]] = 0 /\
    %    (a != b \/ c != d) /\
    %    true
    %  )
    %);
  } in forall (j in NLoci) (
    xs[igz, j] = [xs[igx, j], xs[igy, j]][source[igz, j]]
  )
);

var 0..nTreeCells: objective = count(treeType, Node);
solve :: int_search(
  array1d(xs) ++
    treeType ++
    treeLeft ++
    treeRight ++
    array1d(source) ++
    array1d(swap),
  first_fail,
  indomain_max
) minimize objective;

predicate notDomBy(var NTreeCells: igx, var NTreeCells: igy) = (
  exists(j in NLoci) (xs[igx, j] > xs[igy, j])
);

constraint symmetry_breaking_constraint(
  forall (i in NTreeCells where treeType[i] == Node) (
    %treeLeft[i] < treeRight[i] /\
    notDomBy(i, treeRight[i]) /\
    notDomBy(i, treeLeft[i]) /\
    notDomBy(treeLeft[i], treeRight[i]) /\
    notDomBy(treeRight[i], treeLeft[i]) /\
    true
  )
);
