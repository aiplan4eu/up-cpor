using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace CPOR
{
    class UnixDeadends
    {
        public int Depth { get; set; }
        public int MaxWidth { get; set; }
        public int RandomSeed { get; set; }
        public int Nodes { get; set; }

        public HashSet<int> FilePositions { get; set; }

        public Dictionary<int, List<int>> TreeStructure;
        public HashSet<int> BlockedDirectories;


        private Random Random;

        public string Name { get { return "UnixDeadend" + Depth + "_" + MaxWidth + "_" + RandomSeed; } }

        public UnixDeadends(int iDepth, int iMaxWidth, int cFilePositions, int iRandomSeed)
        {
            Depth = iDepth;
            MaxWidth = iMaxWidth;
            RandomSeed = iRandomSeed;
            Random = new Random(RandomSeed);

            TreeStructure = new Dictionary<int, List<int>>();
            BlockedDirectories = new HashSet<int>();

            Nodes = 1;
            ConstructTree(0, 0);

            FilePositions = new HashSet<int>();
            for (int i = 0; i < cFilePositions; i++)
            {
                int idx = Random.Next(Nodes - 1 + 1);
                FilePositions.Add(idx);
            }

            int cBlocked = Random.Next(Nodes / 5) + 2;
            for (int i = 0; i < cBlocked; i++)
            {
                int iBlocked = Random.Next(Nodes - 1) + 1;
                BlockSubtree(iBlocked);
            }

            while (FilePositions.Intersect(BlockedDirectories).Count() < 2)
            {
                int idx = Random.Next(BlockedDirectories.Count);
                FilePositions.Add(BlockedDirectories.ElementAt(idx));
            }
        }

        private void BlockSubtree(int iBlocked)
        {
            BlockedDirectories.Add(iBlocked);
            if (TreeStructure.ContainsKey(iBlocked))
            {
                foreach (int iSub in TreeStructure[iBlocked])
                    BlockSubtree(iSub);
            }
        }

        private void ConstructTree(int iNode, int iDepth)
        {
            if (iDepth == Depth)
                return;
            if (Nodes >= 1000)
                return;
            int cChildren = Random.Next(MaxWidth - 2) + 2;
            TreeStructure[iNode] = new List<int>();
            for (int i = 0; i < cChildren; i++)
            {
                int iChild = Nodes++;
                TreeStructure[iNode].Add(iChild);
            }
            foreach (int iChild in TreeStructure[iNode])
                ConstructTree(iChild, iDepth + 1);
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
            foreach (int iDir in FilePositions)
                if (BlockedDirectories.Contains(iDir))
                    swProblem.WriteLine("   (and (contains d" + iDir + " f0) (not (HasPermissions d" + iDir + ")))");


            swProblem.WriteLine("))");
            swProblem.Close();
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

            swProblem.WriteLine("(at d0)");
            for (int i = 0; i < Nodes; i++)
            {
                if (TreeStructure.ContainsKey(i))
                {
                    foreach (int j in TreeStructure[i])
                        swProblem.WriteLine("\t (subdir d" + i + " d" + j + ")");
                }
            }


            for (int i = 0; i < Nodes; i++)
            {
                if (!BlockedDirectories.Contains(i))
                    swProblem.WriteLine("\t (HasPermissions d" + i + ")");
                else
                    swProblem.WriteLine("\t (unknown (HasPermissions d" + i + "))");
            }
            swProblem.WriteLine("");

            foreach (int i in BlockedDirectories)
            {
                if (TreeStructure.ContainsKey(i))
                {
                    foreach (int j in TreeStructure[i])
                    {
                        swProblem.WriteLine("\t (or (HasPermissions d" + i + ") (not  (HasPermissions d" + j + ")))");
                    }
                }
            }

            swProblem.WriteLine();

            swProblem.Write("\t (oneof");
            foreach (int i in FilePositions)
            {
                swProblem.Write(" (contains d" + i + " f0)");
            }
            swProblem.WriteLine(")");

            swProblem.WriteLine(")");

            swProblem.WriteLine("");


            swProblem.WriteLine("   (:goal (contains d0 f0))");
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
            swDomain.WriteLine("  (:types dir file)");

            swDomain.WriteLine("  (:constants");
            for (int i = 0; i < Nodes; i++)
            {

                swDomain.Write("d" + i + " ");

            }
            swDomain.WriteLine(" - dir");

            swDomain.WriteLine("   f0 - file");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");


            swDomain.Write("    (:predicates (at ?d - dir)	(subdir ?d1 ?d2 - dir) (contains ?d - dir ?f - file) (HasPermissions ?d - dir) ");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action cd-down");
            swDomain.WriteLine("   :parameters (?d1 - dir ?d2 - dir )");
            swDomain.WriteLine("   :precondition (and (subdir ?d1 ?d2) (at ?d1))");
            swDomain.WriteLine("   :effect  (and (not (at ?d1)) (at ?d2))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action cd-up");
            swDomain.WriteLine("   :parameters (?d1 - dir ?d2 - dir )");
            swDomain.WriteLine("   :precondition (and (subdir ?d1 ?d2) (at ?d2))");
            swDomain.WriteLine("   :effect  (and (not (at ?d2)) (at ?d1))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action check-permissions");
            swDomain.WriteLine("   :parameters (?d - dir)");
            swDomain.WriteLine("   :precondition (and (at ?d) )");
            swDomain.WriteLine("   :observe (HasPermissions ?d)");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action observe-file");
            swDomain.WriteLine("   :parameters (?d - dir ?f - file)");
            swDomain.WriteLine("   :precondition (and (at ?d) )");
            swDomain.WriteLine("   :observe (contains ?d ?f)");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");


            swDomain.WriteLine("  (:action move");
            swDomain.WriteLine("   :parameters (?f - file ?source - dir ?target - dir)");
            swDomain.WriteLine("   :precondition (and (contains ?source ?f) (HasPermissions ?source))");
            swDomain.WriteLine("   :effect (and (contains ?target ?f) (not (contains ?source ?f)))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");




            swDomain.WriteLine(")");

            swDomain.Close();
        }


    }
}
