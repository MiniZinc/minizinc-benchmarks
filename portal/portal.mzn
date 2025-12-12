% This is a MiniZinc model of a portal game.
% The game is played on a 2D grid. The player can move up, down, left, or right.
% The player can also shoot a portal in any direction. The portal will travel in a straight line until it hits a wall.
% The player can then shoot a second portal. If they move onto a portal, they will be teleported to the
% other portal. If they shoot a third portal, the first portal will disappear.

% The player can only shoot one portal at a time. The player can only have two portals on the board at a time.

% The player can only move one square at a time.

% Input data

string: wall = "X";
string: wallNoPortal = "N";
string: empty = " ";
string: pit = "O";
string: playerEast = ">";
string: playerWest = "<";
string: playerNorth = "^";
string: playerSouth = "v";
string: goal = "!";

array[int] of string: inputBoard;

int: height = length(inputBoard);
int: width = string_length(inputBoard[min(index_set(inputBoard))]);

constraint forall (i in index_set(inputBoard)) (
  assert(string_length(inputBoard[i])==width, "Non-rectangular input board")
);

enum Cell = { Wall, WallNoPortal, Empty, Pit };

set of int: W = 1..width;
set of int: H = 1..height;

enum Heading = { North, South, East, West };

tuple(opt Heading, int): playerHeadingAndPos(string: row) =
  let {
    int: n = string_length(row);
    any: cells = string_split(row, "")++[playerNorth,playerSouth,playerEast,playerWest];
    any: pn = min(i in 1..n+4 where cells[i]=playerNorth)(i);
    any: ps = min(i in 1..n+4 where cells[i]=playerSouth)(i);
    any: pe = min(i in 1..n+4 where cells[i]=playerEast)(i);
    any: pw = min(i in 1..n+4 where cells[i]=playerWest)(i);
  } in
  assert((pn <= n)+(ps <= n)+(pe <= n)+(pw <= n) <= 1, "More than one player in this row",
  if pn <= n then (North, pn)
  elseif ps <= n then (South, ps)
  elseif pe <= n then (East, pe)
  elseif pw <= n then (West, pw)
  else (<>, 0) endif
  );
 

array[H, W] of Cell: board = [
  (i,j):
    if cells[j]=wall then Wall
    elseif cells[j]=wallNoPortal then WallNoPortal
    elseif cells[j]=pit then Pit
    else assert(cells[j]=empty \/ cells[j]=playerEast \/ cells[j]=playerWest \/ cells[j]=playerNorth
     \/ cells[j]=playerSouth \/ cells[j]=goal, "Error in \(i),\(j): '\(cells[j])', '\(wall)'", Empty)
    endif
| i in H, cells=string_split(inputBoard[i], ""), j in W
];

type Pos = record(W: x, H: y);
type optPos = record(opt W: x, opt H: y);

any: playerPositions = [ playerHeadingAndPos(inputBoard[i]) | i in H ];

constraint assert(count(p in playerPositions)(occurs(p.1)) = 1,
  "Need exactly one player on the board.");

Pos: playerInitialPos = let {
  H: y = min(i in H where occurs(playerPositions[i].1))(i)
} in (x: playerPositions[y].2, y: y);

Heading: playerInitialHeading = let {
  H: y = min(i in H where occurs(playerPositions[i].1))(i)
} in deopt(playerPositions[y].1);

Pos: goalPos = let {
  any: possibleGoalPositions = [
    let {
      any: row = string_split(inputBoard[i], "")++[goal];
      any: gp = min(j in 1..width+1 where row[j]=goal)(j) }
    in if gp <= width then gp else <> endif
  | i in H];
  constraint assert(count(i in H)(occurs(possibleGoalPositions[i])) = 1,
  "Need exactly one goal on the board.");
  any: gp = min(i in H where occurs(possibleGoalPositions[i]))(i);
} in (x: deopt(possibleGoalPositions[gp]), y: gp);

int: maxTime;
set of int: Time = 1..maxTime;

array[Time] of var Pos: playerPos;
array[Time] of var Heading: playerHeading;

constraint playerPos[min(Time)] == playerInitialPos;
constraint playerHeading[min(Time)] == playerInitialHeading;
constraint playerPos[max(Time)] = goalPos;

array[Time] of var optPos: portal1Pos;
constraint portal1Pos[min(Time)] == (x:<>,y:<>);
array[Time] of var optPos: portal2Pos;
constraint portal2Pos[min(Time)] == (x:<>,y:<>);

enum Action = { Move, Left, Right, Shoot };

array[Time] of var Action: playerAction;

array[Heading, Action] of Heading: newHeadingAction = [
    (North, Left): West, (North, Right): East, (North, Move): North, (North, Shoot): North,
    (South, Left): East, (South, Right): West, (South, Move): South, (South, Shoot): South,
    (East, Left): North, (East, Right): South, (East, Move): East, (East, Shoot): East,
    (West, Left): South, (West, Right): North, (West, Move): West, (West, Shoot): West
];

function var Pos: deltaPos(var Pos: pos, var Heading: heading) =
  let {
    any: deltaX = [North: 0, South:0, East:1, West:-1];
    any: deltaY = [North:-1, South:1, East:0, West: 0];
  } in (x: pos.x + deltaX[heading], y: pos.y + deltaY[heading]);

% For each position on the board and heading, this array stores the position of
% the next wall in that direction.

array[H, W, Heading] of optPos: nextWall = [
    (y,x,h): let {
%         any: wpX = if h==East then min(i in x+1..width where board[y, i] in {Wall, WallNoPortal})(i) default <>
%                   elseif h==West then max(i in 1..x-1 where board[y, i] in {Wall, WallNoPortal})(i) default <>
%                   else x endif;
%         any: wpY = if h==North then max(i in 1..y-1 where board[i, x] in {Wall, WallNoPortal})(i) default <>
%                    elseif h==South then min(i in y+1..height where board[i, x] in {Wall, WallNoPortal})(i) default <>
%                    else y endif;
        any: wpX = [East:min(i in x+1..width where board[y, i] in {Wall, WallNoPortal})(i) default <>,
                    West:max(i in 1..x-1 where board[y, i] in {Wall, WallNoPortal})(i) default <>,
                    North:x,
                    South:x][h];
        any: wpY = [North:max(i in 1..y-1 where board[i, x] in {Wall, WallNoPortal})(i) default <>,
                    South:min(i in y+1..height where board[i, x] in {Wall, WallNoPortal})(i) default <>,
                    East:y,
                    West:y][h];    
    } in if board[wpY, wpX]==Wall then (x:wpX,y:wpY) else (x:<>,y:<>) endif
    | y in H, x in W, h in Heading
];

% constraint trace("nextWall: \(nextWall)\n");
% constraint trace("nextWall:\n"++concat(y in H)(concat(x in W)("\(nextWall[y,x,North]) ")++"\n")++"\n");

% Constraints

constraint forall(t in Time) (
   ( occurs(portal1Pos[t].x) -> portal1Pos[t] != portal2Pos[t] )
/\ board[playerPos[t].y, playerPos[t].x] != Pit
);

constraint forall(t in Time where t < maxTime) (
    let {
        any: oldPos = playerPos[t];
        any: oldHeading = playerHeading[t];
        any: newPos = playerPos[enum_next(t)];
        any: newHeading = playerHeading[enum_next(t)];
        any: portal1 = portal1Pos[t];
        any: newPortal1 = portal1Pos[enum_next(t)];
        any: portal2 = portal2Pos[t];
        any: newPortal2 = portal2Pos[enum_next(t)];
        any: action = playerAction[t];
        any: nextWallPos = nextWall[oldPos.y, oldPos.x, oldHeading];
    } in
    (
        newHeading = newHeadingAction[oldHeading, action]
        /\
        if action == Move then let {
          any: nextPos = deltaPos(oldPos, oldHeading)
        } in
            if portal1 == nextPos then newPos = portal2
            elseif portal2== nextPos then newPos = portal1
            else board[nextPos.y, nextPos.x] == Empty /\ newPos = nextPos
            endif
        else
            newPos = oldPos
        endif /\
        if action == Shoot /\ occurs(nextWallPos.x) then
            newPortal2 = portal1 /\ newPortal1 = nextWallPos
        else
            newPortal1 = portal1 /\ newPortal2 = portal2
        endif
    )
);

any: foundGoalAtStep = min(t in index_set(playerPos) where playerPos[t]=goalPos)(t);

solve
  ::int_search(playerAction, input_order, indomain_min)
minimize foundGoalAtStep;

% Symmetry breaking: last action must be a move, actions after that must be Left

constraint playerAction[to_enum(Time,foundGoalAtStep-1)] = Move;
constraint forall (t in Time where t >= foundGoalAtStep) (
  playerAction[t] = Left
);

% Symmetry breaking: don't immediately turn back, no three turns in a row
constraint forall (t in Time where t < maxTime - 1) (
   ( t < foundGoalAtStep /\ playerAction[t]==Left /\ playerAction[enum_next(t)]==Left
     -> playerAction[enum_next(enum_next(t))]!=Left)
);

predicate preventSequence(array[int] of Action: forbiddenSeq) =
  forall (t in Time where t < maxTime - length(forbiddenSeq)) (
    array1d(playerAction[t..t+length(forbiddenSeq)-1]) != forbiddenSeq
  );

constraint preventSequence([Left,Right]);
constraint preventSequence([Right,Left]);
constraint preventSequence([Right, Right, Right]);

% inputBoard = [
%   "XXXXXXXXXX",
%   "X>  XO   X",
%   "X   X    X",
%   "X   X    X",
%   "X   X    X",
%   "X   X  O X",
%   "X   X O!OX",
%   "X   X    X",
%   "X   X    X",
%   "XXXXXXXXXX",  
% ];
% maxTime = 22;

% playerInitialPos = (x:2,y:2);
% playerInitialHeading = East;
% goalPos = (x:6,y:3);

% inputBoard = [
% "XXXXXX",
% "X> XOX",
% "X  X X",
% "X  X X",
% "X  X!X",
% "XXXXXX",
% ];
% maxTime = 10;


% inputBoard = [
%   "XXXX",
%   "X> X",
%   "X !X",
%   "XXXX"
% ];

% maxTime = 4;


output ["Time:\tPlayer pos:\t\tHeading:\tAction:\tPortal 1 pos:\t\tPortal 2 pos:\n"]++
["\(t+0)\t\(playerPos[t])\t\t\(playerHeading[t])\t\t\(playerAction[t])" 
  ++ "\t\t\(portal1Pos[t])  \t\(portal2Pos[t])\n"
| t in Time where t < fix(foundGoalAtStep)]
++["\(foundGoalAtStep+0)\t\(playerPos[foundGoalAtStep]))\t\t\(playerHeading[foundGoalAtStep])\t\tAt goal\n"]
;

array[Cell] of string: boardToString = [Wall:"X",Pit:"O",WallNoPortal:"N",Empty:" "];
array[Heading] of string: playerToString = [North:"^",South:"v",East:">",West:"<"];

output [
concat(y in H)(concat(x in W)(
  if fix(playerPos[t])=(x:x,y:y) then 
    if goalPos=(x:x,y:y) then "G" else playerToString[fix(playerHeading[t])] endif
  elseif goalPos=(x:x,y:y) then "!"
  elseif fix(portal1Pos[t])=(x:x,y:y) then "1"
  elseif fix(portal2Pos[t])=(x:x,y:y) then "2"
  else boardToString[board[y,x]] endif
)++"\n"
)++"\n\n"
| t in Time where t <= fix(foundGoalAtStep)];
