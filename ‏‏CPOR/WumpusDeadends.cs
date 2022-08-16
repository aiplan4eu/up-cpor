using System;
using System.Collections.Generic;
using System.IO;

namespace CPOR
{
    class WumpusDeadends
    {
        public int Size { get; set; }

        public string Name { get { return "WumpusDeadend" + Size; } }

        public WumpusDeadends(int iSize)
        {
            Size = iSize;
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
            swProblem.WriteLine("   (and (wumpus-at p" + (Size - 1) + "-" + Size + ") (wumpus-at p" + Size + "-" + (Size - 1) + "))");


            swProblem.WriteLine("))");
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

            swProblem.WriteLine("(at p1-1)");
            swProblem.WriteLine("(alive)");
            swProblem.WriteLine("(gold-at p" + Size + "-" + Size + ")");


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
                    if (Math.Abs(i - j) != 1 || (i + j) <= 3)
                        swProblem.WriteLine("   (safe p" + i + "-" + j + ")");
                }
            }
            swProblem.WriteLine("");

            for (int i = 3; i <= Size - 1; i++)
            {
                swProblem.WriteLine("   (oneof (safe p" + i + "-" + (i - 1) + ") (safe p" + (i - 1) + "-" + i + "))");
            }
            swProblem.WriteLine("");

            for (int i = 3; i <= Size; i++)
            {
                swProblem.WriteLine("   (oneof (safe p" + i + "-" + (i - 1) + ") (wumpus-at p" + i + "-" + (i - 1) + "))");
                swProblem.WriteLine("   (oneof (safe p" + (i - 1) + "-" + i + ") (wumpus-at p" + (i - 1) + "-" + i + "))");
            }
            swProblem.WriteLine("");

            swProblem.WriteLine("\t(oneof (stench p1-3 c1) (not (wumpus-at p2-3)))");
            swProblem.WriteLine("\t(oneof (stench p3-1 c1) (not (wumpus-at p3-2)))");
            swProblem.WriteLine("");

            for (int i = 3; i < Size; i++)
            {
                string sPM = "p" + (i - 1) + "-" + (i + 1);
                string sPL = "p" + (i - 1) + "-" + i;
                string sPR = "p" + i + "-" + (i + 1);
                WriteStenches(swProblem, sPM, sPL, sPR);


                sPM = "p" + (i + 1) + "-" + (i - 1);
                sPL = "p" + i + "-" + (i - 1);
                sPR = "p" + (i + 1) + "-" + i;
                WriteStenches(swProblem, sPM, sPL, sPR);



            }
            swProblem.WriteLine(")");

            swProblem.WriteLine("");




            swProblem.WriteLine("   (:goal (and (got-the-treasure) (alive)) )");
            swProblem.WriteLine(")");

            swProblem.Close();
        }

        public void WriteStenches(StreamWriter swProblem, string sPM, string sPL, string sPR)
        {
            //y = (A + D') (B + D') (C' + D') (A + B + C') (A + B' + C) (A' + B + C) (A' + B' + D) (A' + C + D) (B' + C + D) : A=PL, B=PR, C=c1, D=c2
            swProblem.WriteLine("   (or  (wumpus-at " + sPL + ") (not (stench " + sPM + " c2)))");//(A + D')
            swProblem.WriteLine("   (or  (wumpus-at " + sPR + ") (not (stench " + sPM + " c2)))");//(B + D')
            swProblem.WriteLine("   (or  (not (stench " + sPM + " c1)) (not (stench " + sPM + " c2)))");//(C' + D')
            swProblem.WriteLine("   (or  (wumpus-at " + sPL + ") (wumpus-at " + sPR + ") (not (stench " + sPM + " c1)))");//(A + B + C')
            swProblem.WriteLine("   (or  (wumpus-at " + sPL + ") (not (wumpus-at " + sPR + ")) (stench " + sPM + " c1))");//(A + B' + C)
            swProblem.WriteLine("   (or  (not (wumpus-at " + sPL + ")) (wumpus-at " + sPR + ") (stench " + sPM + " c1))");//(A' + B + C)
            swProblem.WriteLine("   (or  (not (wumpus-at " + sPL + ")) (not (wumpus-at " + sPR + ")) (stench " + sPM + " c2))"); //(A' + B' + D)
            swProblem.WriteLine("   (or  (not (wumpus-at " + sPL + "))  (stench " + sPM + " c1) (stench " + sPM + " c2))"); //(A' + C + D)
            swProblem.WriteLine("   (or  (not (wumpus-at " + sPR + "))  (stench " + sPM + " c1) (stench " + sPM + " c2))"); //(B' + C + D)
            swProblem.WriteLine("");

        }

        public void WriteDomain(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swDomain = new StreamWriter(sPath + "/d.pddl");
            swDomain.WriteLine("(define (domain " + Name + ")");
            swDomain.WriteLine("  (:types pos count)");

            swDomain.WriteLine("  (:constants");
            for (int i = 1; i <= Size; i++)
            {
                for (int j = 1; j <= Size; j++)
                {
                    swDomain.Write("p" + i + "-" + j + " ");
                }
            }
            swDomain.WriteLine(" - pos");

            swDomain.WriteLine("    c0 c1 c2 - count");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");


            swDomain.WriteLine("    (:predicates 	(adj ?i ?j - pos) (at ?i - pos) (safe ?i - pos) ");
            swDomain.WriteLine("				(wumpus-at ?x - pos) (alive) (stench ?i - pos ?c - count)");
            swDomain.WriteLine("				(gold-at ?i - pos) (got-the-treasure)");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action move");
            swDomain.WriteLine("   :parameters (?i - pos ?j - pos )");
            swDomain.WriteLine("   :precondition (and (adj ?i ?j) (at ?i) (alive) (safe ?j) (safe ?i) )");
            swDomain.WriteLine("   :effect  (and (not (at ?i)) (at ?j))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action smell_wumpus");
            swDomain.WriteLine("   :parameters (?pos - pos ?c - count)");
            swDomain.WriteLine("   :precondition (and (alive) (at ?pos) )");
            swDomain.WriteLine("   :observe (stench ?pos ?c)");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");


            swDomain.WriteLine("  (:action grab");
            swDomain.WriteLine("   :parameters (?i - pos)");
            swDomain.WriteLine("   :precondition (and (at ?i) (gold-at ?i) (alive))");
            swDomain.WriteLine("   :effect (and (got-the-treasure) (not (gold-at ?i)))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");




            swDomain.WriteLine(")");

            swDomain.Close();
        }


    }
}
