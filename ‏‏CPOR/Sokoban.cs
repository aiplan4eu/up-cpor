using System;
using System.Collections.Generic;
using System.IO;

namespace CPOR
{
    class Sokoban
    {
        public int Size;
        public int Index;
        public int Stones;
        public int Deadends;
        public int Uncertain;

        public string Name
        {
            get
            {
                return "Sokoban-" + Size + "-" + Stones + "-" + Deadends + "-" + Uncertain + "-" + Index;
            }
        }

        private Random m_rGen;

        private int[,] Maze;

        public Sokoban(int iSize, int cStones, int cDeadends, int cUncertain, int iIndex)
        {
            Size = iSize;
            Stones = cStones;
            Deadends = cDeadends;
            Uncertain = cUncertain;
            Index = iIndex;
            m_rGen = new Random(Index);
            Maze = new int[Size + 1, Size + 1];
            //walls
            Maze[0, 0] = 1;
            for (int i = 1; i < Size; i++)
            {
                for (int j = 1; j < Size; j++)
                {
                    double dRand = m_rGen.NextDouble();
                    if (dRand < 0.1)
                        Maze[i, j] = 1;
                    else
                        Maze[i, j] = 0;
                }
            }
            //Start positions
            for (int i = 1; i <= cStones; i++)
            {
                int xStart = 0, yStart = 0, xEnd = 0, yEnd = 0;
                while (Maze[xStart, yStart] != 0)
                {
                    xStart = m_rGen.Next(Size - 2) + 2;
                    yStart = m_rGen.Next(Size - 2) + 2;
                }
                Maze[xStart, yStart] = i * 10 + 1;
                while (Maze[xEnd, yEnd] != 0)
                {
                    xEnd = m_rGen.Next(Size) + 1;
                    yEnd = m_rGen.Next(Size) + 1;
                }
                Maze[xEnd, yEnd] = i * 10 + 5;
                if (i <= Deadends)
                {
                    if (xEnd == 1 && Maze[Size, yStart] == 0)
                    {
                        Maze[Size, yStart] = i * 10 + 2;
                    }
                    else if (xEnd == Size && Maze[1, yStart] == 0)
                    {
                        Maze[1, yStart] = i * 10 + 2;
                    }
                    else if (yEnd == 1 && Maze[xStart, Size] == 0)
                    {
                        Maze[xStart, Size] = i * 10 + 2;
                    }
                    else if (yEnd == Size && Maze[xStart, 1] == 0)
                    {
                        Maze[xStart, 1] = i * 10 + 2;
                    }
                    else if (Maze[xStart, Size] == 0)
                    {
                        Maze[xStart, Size] = i * 10 + 2;
                    }
                }
                else if (i <= Uncertain)
                {
                    while (Maze[xStart, yStart] != 0)
                    {
                        xStart = m_rGen.Next(Size - 2) + 2;
                        yStart = m_rGen.Next(Size - 2) + 2;
                    }
                    Maze[xStart, yStart] = i * 10 + 3;
                }
            }
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
            for (int iStone = 1; iStone <= Stones; iStone++)
            {
                for (int x = 1; x <= Size; x++)
                {
                    for (int y = 1; y <= Size; y++)
                    {
                        if (Maze[x, y] == iStone * 10 + 2)
                        {
                            swProblem.WriteLine("        (init-at s" + iStone + " p" + x + "-" + y + ")");
                        }
                    }
                }
            }


            swProblem.WriteLine(")");
            swProblem.WriteLine(")");
            swProblem.Close();
        }


        List<string> GetAdj(int i, int j)
        {
            List<string> lAdj = new List<string>();
            if (i > 1)
                lAdj.Add("(adj p" + i + "-" + j + " p" + (i - 1) + "-" + j + ")");
            if (i < Size)
                lAdj.Add("(adj p" + i + "-" + j + " p" + (i + 1) + "-" + j + ")");
            if (j > 1)
                lAdj.Add("(adj p" + i + "-" + j + " p" + i + "-" + (j - 1) + ")");
            if (j < Size)
                lAdj.Add("(adj p" + i + "-" + j + " p" + i + "-" + (j + 1) + ")");
            return lAdj;
        }

        List<string> GetCanPush(int i, int j)
        {
            List<string> lAdj = new List<string>();
            if (i > 2)
                lAdj.Add("(can-push p" + i + "-" + j + " p" + (i - 1) + "-" + j + " p" + (i - 2) + "-" + j + ")");
            if (i < Size - 1)
                lAdj.Add("(can-push p" + i + "-" + j + " p" + (i + 1) + "-" + j + " p" + (i + 2) + "-" + j + ")");
            if (j > 2)
                lAdj.Add("(can-push p" + i + "-" + j + " p" + i + "-" + (j - 1) + " p" + i + "-" + (j - 2) + ")");
            if (j < Size - 1)
                lAdj.Add("(can-push p" + i + "-" + j + " p" + i + "-" + (j + 1) + " p" + i + "-" + (j + 2) + ")");
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

            swProblem.WriteLine("(at p0 p1-1)");


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

            for (int i = 1; i <= Size; i++)
            {
                for (int j = 1; j <= Size; j++)
                {

                    List<string> lCanPush = GetCanPush(i, j);
                    foreach (string s in lCanPush)
                        swProblem.WriteLine("\t" + s);
                }
            }
            swProblem.WriteLine("");

            string sBlocked = ";; Blocked = ";
            for (int x = 1; x <= Size; x++)
            {
                for (int y = 1; y <= Size; y++)
                {
                    if (Maze[x, y] == 0 || Maze[x, y] % 5 == 0)
                        swProblem.WriteLine("   (clear p" + x + "-" + y + ")");
                    if (Maze[x, y] == 1)
                        sBlocked += " (" + x + "," + y + ")";
                }
            }

            swProblem.WriteLine(sBlocked);
            swProblem.WriteLine("");

            for (int iStone = 1; iStone <= Stones; iStone++)
            {
                List<string> lStartPositions = new List<string>();

                for (int x = 1; x <= Size; x++)
                {
                    for (int y = 1; y <= Size; y++)
                    {
                        if (Maze[x, y] > iStone * 10 && Maze[x, y] < iStone * 10 + 5)
                        {
                            lStartPositions.Add("p" + x + "-" + y);
                        }
                    }
                }
                if (lStartPositions.Count > 1)
                {
                    swProblem.Write("\t(oneof");
                    foreach (string s in lStartPositions)
                        swProblem.Write(" (init-at s" + iStone + " " + s + ")");
                    swProblem.WriteLine(")");
                    swProblem.WriteLine("\t(at s" + iStone + " out)");
                    foreach (string s in lStartPositions)
                    {
                        swProblem.WriteLine("\t(clear " + s + ")");
                    }
                }
                else
                {
                    swProblem.WriteLine("\t(at s" + iStone + " " + lStartPositions[0] + ")");
                    swProblem.WriteLine("\t(init-at s" + iStone + " " + lStartPositions[0] + ")");
                }
                swProblem.WriteLine("");
            }




            swProblem.WriteLine(")");

            swProblem.WriteLine("");




            swProblem.Write("   (:goal (and ");

            for (int iStone = 1; iStone <= Stones; iStone++)
            {
                for (int x = 1; x <= Size; x++)
                {
                    for (int y = 1; y <= Size; y++)
                    {
                        if (Maze[x, y] == iStone * 10 + 5)
                        {
                            swProblem.Write(" (at s" + iStone + " p" + x + "-" + y + ")");
                        }
                    }
                }
            }
            swProblem.WriteLine("))");

            swProblem.WriteLine(")");

            swProblem.Close();
        }

        public void WriteDomain(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swDomain = new StreamWriter(sPath + "/d.pddl");
            swDomain.WriteLine("(define (domain " + Name + ")");
            swDomain.WriteLine("  (:types obj pos)");

            swDomain.WriteLine("  (:constants");
            for (int i = 1; i <= Size; i++)
            {
                for (int j = 1; j <= Size; j++)
                {
                    swDomain.Write("p" + i + "-" + j + " ");
                }
            }
            swDomain.Write("out");
            swDomain.WriteLine(" - pos");

            swDomain.Write("    p0");
            for (int iStone = 1; iStone <= Stones; iStone++)
            {
                swDomain.Write(" s" + iStone);

            }
            swDomain.WriteLine(" - obj");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");


            swDomain.WriteLine("    (:predicates 	(adj ?i ?j - pos) (can-push ?i ?j ?k - pos) (init-at ?o - obj ?i - pos) (at ?o - obj ?i - pos) (clear ?i - pos) ");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action move");
            swDomain.WriteLine("   :parameters (?i - pos ?j - pos )");
            swDomain.WriteLine("   :precondition (and (adj ?i ?j) (at p0 ?i) (clear ?j))");
            swDomain.WriteLine("   :effect  (and (not (at p0 ?i)) (at p0 ?j) (not (clear ?j)) (clear ?i))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action push");
            swDomain.WriteLine("   :parameters (?s - obj ?i - pos ?j - pos ?k - pos )");
            swDomain.WriteLine("   :precondition (and (can-push ?i ?j ?k) (at p0 ?i) (at ?s ?j) (clear ?k))");
            swDomain.WriteLine("   :effect  (and (not (at p0 ?i)) (at p0 ?j) (not (at ?s ?j)) (at ?s ?k) (not (clear ?k)) (clear ?i))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");



            swDomain.WriteLine("  (:action observe-stone-init");
            swDomain.WriteLine("   :parameters (?s - obj ?i - pos ?j - pos )");
            swDomain.WriteLine("   :precondition (and (adj ?i ?j) (at p0 ?i))");
            swDomain.WriteLine("   :observe  (init-at ?s ?j)");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            /*
            swDomain.WriteLine("  (:action reset-stone");
            swDomain.WriteLine("   :parameters (?s - obj ?i - pos ?j - pos )");
            swDomain.WriteLine("   :precondition (and (at ?s ?i) (clear ?j))");
            swDomain.WriteLine("   :effect  (when (init-at ?s ?j) (and (not (at ?s ?i)) (at ?s ?j)))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");
            */

            swDomain.WriteLine("  (:action reset-stone");
            swDomain.WriteLine("   :parameters (?s - obj ?i - pos ?j - pos )");
            swDomain.WriteLine("   :precondition (and (at ?s ?i) (clear ?j) (init-at ?s ?j))");
            swDomain.WriteLine("   :effect  (and (not (at ?s ?i)) (clear ?i) (at ?s ?j) (not (clear ?j)))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");



            swDomain.WriteLine(")");

            swDomain.Close();
        }


    }
}
