using System;
using System.Collections.Generic;
using System.IO;

namespace CPOR
{
    class Cavediving
    {
        public int Size;
        public int Index;
        public int Paths;
        public int Tanks;
        public int Quantity;

        public string Name
        {
            get
            {
                if (DeadendLimit == -1)
                    return "Cavediving-" + Size + "-" + Paths + "-" + Quantity + "-" + Index;
                else
                    return "Cavediving-" + Size + "-" + Paths + "-" + Quantity + "-" + DeadendLimit + "-" + Index;
            }
        }

        public enum Cell { Unreachable, Reachable, Tank, UncertainTank };

        private Random m_rGen;

        private Cell[,] Maze;

        public class Position
        {
            public int Tank;
            public int Quantity;

            public Position(int iX, int iY)
            {
                X = iX;
                Y = iY;
            }
            public Position(int iX, int iY, int iQuantity)
            {
                X = iX;
                Y = iY;
                Quantity = iQuantity;
            }

            public int X, Y;

            public Position Plus(int dX, int dY)
            {
                return new Position(X + dX, Y + dY, Quantity - 1);
            }

            public bool Valid(int iSize)
            {
                return X > 0 && X <= iSize && Y > 0 && Y <= iSize;
            }

            public override bool Equals(object obj)
            {
                if (obj is Position p)
                {
                    return p.X == X && p.Y == Y;
                }
                return false;
            }

            public override string ToString()
            {
                return "(" + X + "," + Y + ")";
            }

            public override int GetHashCode()
            {
                return X * 1000 + Y;
            }
        }

        public int DeadendLimit { get; set; }

        public Cavediving(int iSize, int cPaths, int cQuantity, int iIndex, int cDeadends = -1)
        {
            DeadendLimit = cDeadends;
            Size = iSize;
            Paths = cPaths;
            Index = iIndex;
            Quantity = cQuantity;
            m_rGen = new Random(Index);
            Maze = new Cell[Size + 1, Size + 1];

            for (int iPath = 0; iPath < Paths; iPath++)
            {
                int x = 1, y = 1;
                List<Position> lPath = new List<Position>();
                lPath.Add(new Position(x, y));
                while (x != Size || y != Size)
                {
                    int xStep = m_rGen.Next(Quantity + 1);
                    int yStep = m_rGen.Next(Quantity + 1);
                    if (x < Size && m_rGen.NextDouble() < 0.5)
                    {
                        x = x + xStep;
                        if (x > Size)
                            x = Size;
                    }
                    else
                    {
                        y = y + yStep;
                        if (y > Size)
                            y = Size;
                    }
                    lPath.Add(new Position(x, y));
                }
                for (int i = 0; i < lPath.Count; i++)
                {
                    Maze[lPath[i].X, lPath[i].Y] = Cell.Tank;
                    for (int j = -Quantity; j <= Quantity; j++)
                    {
                        Position pNew = lPath[i].Plus(j, 0);
                        if (pNew.Valid(Size) && Maze[pNew.X, pNew.Y] != Cell.Tank)
                            Maze[pNew.X, pNew.Y] = Cell.Reachable;
                        pNew = lPath[i].Plus(0, j);
                        if (pNew.Valid(Size) && Maze[pNew.X, pNew.Y] != Cell.Tank)
                            Maze[pNew.X, pNew.Y] = Cell.Reachable;
                    }
                }
            }

            int iRow1 = m_rGen.Next(Size - Quantity) + 1;
            for (int x = 0; x <= Size; x++)
            {
                for (int i = 0; i < Quantity; i++)
                {
                    if (Maze[x, iRow1 + i] == Cell.Tank)
                        Maze[x, iRow1 + i] = Cell.UncertainTank;
                }
            }

            int iCol1 = m_rGen.Next(Size - Quantity) + 1;
            for (int y = 0; y <= Size; y++)
            {
                for (int i = 0; i < Quantity; i++)
                {
                    if (Maze[iCol1 + i, y] == Cell.Tank)
                        Maze[iCol1 + i, y] = Cell.UncertainTank;
                }
            }

            Maze[1, 1] = Cell.Tank;
            Maze[iSize, iSize] = Cell.Reachable;

            List<Position> lUncertain = new List<Position>();

            Tanks = 0;
            for (int i = 1; i <= Size; i++)
            {
                for (int j = 1; j <= Size; j++)
                {
                    if (Maze[i, j] == Cell.Tank || Maze[i, j] == Cell.UncertainTank)
                        Tanks++;
                    if (Maze[i, j] == Cell.UncertainTank)
                    {
                        Position p = new Position(i, j);
                        p.Tank = Tanks;
                        lUncertain.Add(p);
                    }
                }
            }
            Deadends = FindDeadends(lUncertain);
        }

        public List<List<Position>> Deadends;

        public List<List<Position>> FindDeadends(List<Position> lUncertain)
        {
            int cUncertain = lUncertain.Count;
            List<List<Position>> lDeadends = new List<List<Position>>();
            for (int i = 0; i < Math.Pow(2, cUncertain); i++)
            {
                Cell[,] aMaze = (Cell[,])Maze.Clone();
                List<Position> lDeadend = new List<Position>();
                int positions = i;
                for (int j = 0; j < cUncertain; j++)
                {
                    Position p = lUncertain[j];
                    if (positions % 2 == 1)
                    {
                        aMaze[p.X, p.Y] = Cell.Tank;
                    }
                    else
                    {
                        lDeadend.Add(p);
                        aMaze[p.X, p.Y] = Cell.Reachable;
                    }
                    positions = positions / 2;
                }
                if (!BFS(aMaze))
                {
                    lDeadends.Add(lDeadend);
                    //if (lDeadends.Count > 10)
                    //   Console.Write("*");
                }
            }
            List<List<Position>> lFiltered = new List<List<Position>>();
            foreach (List<Position> lDeadend in lDeadends)
            {
                bool bContainsReduced = false;
                for (int i = 0; i < lDeadend.Count && !bContainsReduced; i++)
                {
                    List<Position> lReduced = new List<Position>();
                    for (int j = 0; j < lDeadend.Count; j++)
                        if (i != j)
                            lReduced.Add(lDeadend[j]);
                    if (Contains(lDeadends, lReduced))
                        bContainsReduced = true;
                }
                if (!bContainsReduced)
                    lFiltered.Add(lDeadend);
            }
            return lFiltered;
        }

        public bool Contains(List<List<Position>> lDeadends, List<Position> lDeadend)
        {
            foreach (List<Position> l in lDeadends)
            {
                if (Equals(l, lDeadend))
                    return true;
            }
            return false;
        }
        public bool Equals(List<Position> l1, List<Position> l2)
        {
            if (l1.Count != l2.Count)
                return false;
            foreach (Position p in l1)
                if (!l2.Contains(p))
                    return false;
            return true;
        }
        public bool BFS(Cell[,] aMaze)
        {
            Queue<Position> qOpen = new Queue<Position>();
            List<Position> lVisited = new List<Position>();
            qOpen.Enqueue(new Position(1, 1, 2));
            while (qOpen.Count > 0)
            {
                Position p = qOpen.Dequeue();
                if (!p.Valid(Size))
                    continue;
                if (p.Quantity == 0 && aMaze[p.X, p.Y] != Cell.Tank)
                    continue;
                if (aMaze[p.X, p.Y] == Cell.Tank)
                {
                    p = new Position(p.X, p.Y, Quantity);
                }
                for (int i = -1; i <= 1; i++)
                {
                    if (i == 0)
                        continue;
                    Position pNext = p.Plus(i, 0);
                    if (pNext.X == Size && pNext.Y == Size)
                        return true;
                    if (!BFSContains(lVisited, pNext))
                    {
                        Add(lVisited, pNext);
                        if (pNext.Valid(Size))
                            qOpen.Enqueue(pNext);
                    }
                    pNext = p.Plus(0, i);
                    if (pNext.X == Size && pNext.Y == Size)
                        return true;
                    if (!BFSContains(lVisited, pNext))
                    {
                        Add(lVisited, pNext);
                        if (pNext.Valid(Size))
                            qOpen.Enqueue(pNext);
                    }
                }
            }
            return false;
        }

        private void Add(List<Position> l, Position p)
        {
            l.Add(p);
        }

        private bool BFSContains(List<Position> l, Position p)
        {
            foreach (Position pTag in l)
            {
                if (pTag.X == p.X && pTag.Y == p.Y)
                {
                    if (pTag.Quantity == p.Quantity)
                        return true;
                }

            }
            return false;
        }

        public void WriteDeadends(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swProblem = new StreamWriter(sPath + "/dead.pddl");
            swProblem.WriteLine("(define (problem deadends_" + Name + ")");
            swProblem.WriteLine("  (:domain " + Name + ")");
            swProblem.WriteLine("(:init ");

            if (Deadends.Count > 0)
            {
                for (int i = 0; i < Deadends.Count; i++)
                {
                    if (i == DeadendLimit)
                        break;
                    List<Position> lDeadend = Deadends[i];
                    swProblem.Write("\t(and");
                    foreach (Position p in lDeadend)
                        swProblem.Write(" (init-quantity t" + p.Tank + " n0)");
                    swProblem.WriteLine(")");
                }
            }

            swProblem.WriteLine(")");
            swProblem.WriteLine(")");
            swProblem.Close();
        }


        List<string> GetAdj(int i, int j)
        {
            List<string> lAdj = new List<string>();
            if (Maze[i, j] == Cell.Unreachable)
                return lAdj;
            if (i > 1 && Maze[i - 1, j] != Cell.Unreachable)
                lAdj.Add("(adj p" + i + "-" + j + " p" + (i - 1) + "-" + j + ")");
            if (i < Size && Maze[i + 1, j] != Cell.Unreachable)
                lAdj.Add("(adj p" + i + "-" + j + " p" + (i + 1) + "-" + j + ")");
            if (j > 1 && Maze[i, j - 1] != Cell.Unreachable)
                lAdj.Add("(adj p" + i + "-" + j + " p" + i + "-" + (j - 1) + ")");
            if (j < Size && Maze[i, j + 1] != Cell.Unreachable)
                lAdj.Add("(adj p" + i + "-" + j + " p" + i + "-" + (j + 1) + ")");
            return lAdj;
        }

        public void WriteProblem(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swProblem = new StreamWriter(sPath + "/p.pddl");
            swProblem.WriteLine("(define (problem " + Name + ")");
            swProblem.WriteLine("  (:domain " + Name + ")");

            swProblem.WriteLine("(:init ");

            string sMaxQuantity = "n" + Quantity;

            swProblem.WriteLine("(can-init)");

            swProblem.WriteLine("(at d0 p1-1)");
            swProblem.WriteLine("(quantity d0 n" + Quantity + ")");

            for (int i = 0; i < Quantity; i++)
            {
                swProblem.WriteLine("(next n" + i + " n" + (i + 1) + ")");
            }

            for (int i = 1; i <= Size; i++)
            {
                for (int j = 1; j <= Size; j++)
                {

                    List<string> lAdj = GetAdj(i, j);
                    foreach (string s in lAdj)
                        swProblem.WriteLine("\t" + s);
                }
            }
            swProblem.WriteLine("");
            int iTank = 1;
            string sFull = "";

            if (DeadendLimit >= 0)
            {
                for (int i = DeadendLimit; i < Deadends.Count; i++)
                {
                    List<Position> lDeadend = Deadends[i];
                    string sOneof = "\t(oneof ";
                    foreach (Position p in lDeadend)
                    {
                        sOneof += " (init-quantity t" + p.Tank + " " + sMaxQuantity + ")";
                    }
                    sOneof += ")";
                    swProblem.WriteLine(sOneof);
                }
            }

            for (int x = 1; x <= Size; x++)
            {
                for (int y = 1; y <= Size; y++)
                {
                    if (Maze[x, y] == Cell.UncertainTank || Maze[x, y] == Cell.Tank)
                    {
                        swProblem.WriteLine("   (at t" + iTank + " p" + x + "-" + y + ")");
                        if (Maze[x, y] == Cell.UncertainTank)
                        {
                            sFull += "\t(oneof (init-quantity t" + iTank + " n0) (init-quantity t" + iTank + " " + sMaxQuantity + "))\n";

                            sFull += "\t(or (not (init-quantity t" + iTank + " n0)) (quantity t" + iTank + " n0))\n";
                            sFull += "\t(or (not (quantity t" + iTank + " n0)) (init-quantity t" + iTank + " n0))\n";

                            sFull += "\t(or (not (init-quantity t" + iTank + " " + sMaxQuantity + ")) (quantity t" + iTank + " " + sMaxQuantity + "))\n";
                            sFull += "\t(or (not (quantity t" + iTank + " " + sMaxQuantity + ")) (init-quantity t" + iTank + " " + sMaxQuantity + "))\n";
                        }
                        else
                        {
                            sFull += "\t(quantity t" + iTank + " " + sMaxQuantity + ")\n";
                            sFull += "\t(init-quantity t" + iTank + " " + sMaxQuantity + ")\n";
                        }

                        iTank++;
                    }
                }
            }
            swProblem.WriteLine("");
            swProblem.WriteLine(sFull);
            swProblem.WriteLine("");

            swProblem.WriteLine(")");

            swProblem.WriteLine("");



            swProblem.Write("   (:goal (at d0 p" + Size + "-" + Size + "))");


            swProblem.WriteLine(")");

            swProblem.Close();
        }

        public void WriteDomain(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }

            string sMaxQuantity = "n" + Quantity;

            StreamWriter swDomain = new StreamWriter(sPath + "/d.pddl");
            swDomain.WriteLine("(define (domain " + Name + ")");
            swDomain.WriteLine("  (:types obj pos number)");

            swDomain.WriteLine("  (:constants");
            for (int i = 1; i <= Size; i++)
            {
                for (int j = 1; j <= Size; j++)
                {
                    swDomain.Write("p" + i + "-" + j + " ");
                }
            }
            swDomain.WriteLine(" - pos");

            swDomain.Write("    d0");
            for (int iTank = 1; iTank <= Tanks; iTank++)
            {
                swDomain.Write(" t" + iTank);

            }
            swDomain.WriteLine(" - obj");
            for (int i = 0; i <= Quantity; i++)
                swDomain.Write(" n" + i);
            swDomain.WriteLine(" - number");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");


            swDomain.WriteLine("    (:predicates 	(adj ?i ?j - pos)  (init-quantity ?o - obj ?n - number) (at ?o - obj ?i - pos) (quantity ?o - obj ?n - number) (next ?n - number ?n - number) (can-init)");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action swim");
            swDomain.WriteLine("   :parameters (?i - pos ?j - pos ?q1 - number ?q2 - number )");
            swDomain.WriteLine("   :precondition (and (adj ?i ?j) (at d0 ?i) (quantity d0 ?q2) (next ?q1 ?q2))");
            swDomain.WriteLine("   :effect  (and (not (at d0 ?i)) (at d0 ?j) (not (quantity d0 ?q2)) (quantity d0 ?q1))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action fill-from-tank");
            swDomain.WriteLine("   :parameters (?t - obj ?i - pos ?n1 - number ?n2 - number)");
            swDomain.WriteLine("   :precondition (and (at d0 ?i) (at ?t ?i) (not (quantity ?t n0)) (quantity ?t ?n1) (quantity d0 ?n2) (not (quantity d0 ?n1)))");
            swDomain.WriteLine("   :effect  (and (not (quantity ?t ?n1))  (quantity ?t n0) (not (quantity d0 ?n2)) (quantity d0 ?n1))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");



            swDomain.WriteLine("  (:action observe-tank");
            swDomain.WriteLine("   :parameters (?t - obj ?n - number ?i - pos)");
            swDomain.WriteLine("   :precondition (and (at ?t ?i)  (at d0 ?i))");
            swDomain.WriteLine("   :observe  (quantity ?t ?n)");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");



            swDomain.WriteLine("  (:action reset-tank");
            swDomain.WriteLine("   :parameters (?t - obj ?n1 - number)");
            swDomain.WriteLine("   :precondition (and (at d0 p1-1) (init-quantity ?t ?n1) (quantity ?t n0) (not  (init-quantity ?t n0)))");
            swDomain.WriteLine("   :effect  (and (not (quantity ?t n0)) (quantity ?t ?n1))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action reset-diver");
            swDomain.WriteLine("   :parameters (?i - pos)");
            swDomain.WriteLine("   :precondition (and (at d0 ?i) (not (at d0 p1-1)))");
            swDomain.WriteLine("   :effect  (and (not (at d0 ?i)) (at d0 p1-1))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");


            /*

            swDomain.WriteLine("  (:action reset-diver");
            swDomain.WriteLine("   :parameters (?i - pos)");
            swDomain.WriteLine("   :precondition (and (at d0 ?i) (quantity d0 n0) (not (at d0 p1-1)))");
            swDomain.WriteLine("   :effect  (and (not (at d0 ?i)) (at d0 p1-1) (not (quantity d0 n0)) (quantity d0 " + sMaxQuantity + "))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action reset-tank");
            swDomain.WriteLine("   :parameters (?t - obj ?i - pos ?n1 - number ?n2 - number)");
            swDomain.WriteLine("   :precondition (and (at d0 ?i) (init-quantity ?t ?n1) (quantity ?t ?n2) (not (init-quantity ?t ?n2)))");
            swDomain.WriteLine("   :effect  (and (not (at d0 ?i)) (at d0 p1-1) (not (quantity ?t ?n2)) (quantity ?t ?n1))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

                       swDomain.WriteLine("  (:action reset-tank");
                       swDomain.WriteLine("   :parameters (?t - obj ?n1 - number ?n2 - number)");
                       swDomain.WriteLine("   :precondition (and (at d0 p1-1) (init-quantity ?t ?n1) (quantity ?t ?n2) (not (init-quantity ?t ?n2)))");
                       swDomain.WriteLine("   :effect  (and (not (quantity ?t ?n2)) (quantity ?t ?n1) (can-init))");
                       swDomain.WriteLine("  )");
                       swDomain.WriteLine("");


                       swDomain.WriteLine("  (:action reset-diver");
                       swDomain.WriteLine("   :parameters (?t - obj ?i - pos)");
                       swDomain.WriteLine("   :precondition (and (at d0 ?i) (quantity d0 n0) (not (at d0 p1-1)) (can-init))");
                       swDomain.WriteLine("   :effect  (and (not (at d0 ?i)) (at d0 p1-1) (not (quantity d0 n0)) (quantity d0 " + sMaxQuantity + ") (not (can-init)))");
                       swDomain.WriteLine("  )");
                       swDomain.WriteLine("");


                       swDomain.WriteLine("  (:action reset-diver");
                       swDomain.WriteLine("   :parameters (?t - obj ?i - pos)");
                       swDomain.WriteLine("   :precondition (and (at d0 ?i) (quantity d0 n0) (not (at d0 p1-1)))");
                       swDomain.WriteLine("   :effect  (and (not (at d0 ?i)) (at d0 p1-1) (not (quantity d0 n0)) (quantity d0 " + sMaxQuantity + "))");
                       swDomain.WriteLine("  )");
                       swDomain.WriteLine("");
                       */

            swDomain.WriteLine(")");

            swDomain.Close();
        }

    }
}
