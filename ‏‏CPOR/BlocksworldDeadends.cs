using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace CPOR
{
    class BlocksworldDeadends
    {
        public int Size { get; set; }
        public int Heavy { get; set; }
        public int Reductions { get; set; }

        public int RandomSeed { get; set; }

        public string Name
        {
            get
            {
                if (DeadendLimit == -1)

                    return "BlocksworldDeadends" + Size + "_" + Heavy + "_" + Reductions + "_" + RandomSeed;
                else
                    return "BlocksworldDeadends" + Size + "_" + Heavy + "_" + Reductions + "_" + DeadendLimit + "_" + RandomSeed;
            }
        }

        Random Random;


        List<List<int>> InitialTowers;
        List<int> FinalTower;
        HashSet<int> HeavyRelevantBlocks;
        HashSet<int> HeavyIrrelvantBlocks;
        HashSet<int> RelevantBlocks;
        HashSet<int> IrrelevantBlocks;

        public int DeadendLimit;

        public BlocksworldDeadends(int iSize, int cHeavy, int cReductions, int iRandomSeed, int iDeadendLimit = -1)
        {
            DeadendLimit = iDeadendLimit;
            Size = iSize;
            Heavy = cHeavy;
            Reductions = cReductions;
            RandomSeed = iRandomSeed;
            Random = new Random(RandomSeed);

            InitialTowers = new List<List<int>>();
            int cTowers = Random.Next(Size / 5) + 2;
            for (int i = 0; i < cTowers; i++)
                InitialTowers.Add(new List<int>());
            for (int i = 0; i < Size; i++)
            {
                int iTower = Random.Next(cTowers);
                InitialTowers[iTower].Add(i);
            }
            int cFinalTower = Random.Next(5) + 2;
            FinalTower = new List<int>();
            while (FinalTower.Count < cFinalTower)
            {
                int iBlock = Random.Next(Size);
                if (!FinalTower.Contains(iBlock))
                    FinalTower.Add(iBlock);
            }
            RelevantBlocks = new HashSet<int>();
            IrrelevantBlocks = new HashSet<int>();
            for (int iTower = 0; iTower < cTowers; iTower++)
            {
                bool bRelevant = false;
                for (int i = 0; i < InitialTowers[iTower].Count; i++)
                {
                    int iBlock = InitialTowers[iTower][i];
                    if (FinalTower.Contains(iBlock))
                        bRelevant = true;
                    if (bRelevant)
                        RelevantBlocks.Add(iBlock);
                    else
                        IrrelevantBlocks.Add(iBlock);
                }
            }
            if (DeadendLimit == -1)
            {
                if (cHeavy >= RelevantBlocks.Count)
                    cHeavy = RelevantBlocks.Count - 1;
                HeavyRelevantBlocks = new HashSet<int>();
                while (HeavyRelevantBlocks.Count < cHeavy)
                {
                    int idx = Random.Next(RelevantBlocks.Count);
                    HeavyRelevantBlocks.Add(RelevantBlocks.ElementAt(idx));
                }
                int cHeavyBlocks = Random.Next(IrrelevantBlocks.Count / 2);
                HeavyIrrelvantBlocks = new HashSet<int>();
                while (HeavyIrrelvantBlocks.Count < cHeavyBlocks)
                {
                    int idx = Random.Next(IrrelevantBlocks.Count);
                    HeavyIrrelvantBlocks.Add(IrrelevantBlocks.ElementAt(idx));
                }
            }
            else
            {
                HeavyRelevantBlocks = new HashSet<int>();
                while (HeavyRelevantBlocks.Count < DeadendLimit)
                {
                    int idx = Random.Next(RelevantBlocks.Count);
                    HeavyRelevantBlocks.Add(RelevantBlocks.ElementAt(idx));
                }
                int cHeavyBlocks = Heavy - DeadendLimit;
                HeavyIrrelvantBlocks = new HashSet<int>();
                while (HeavyIrrelvantBlocks.Count < cHeavyBlocks)
                {
                    int idx = Random.Next(IrrelevantBlocks.Count);
                    HeavyIrrelvantBlocks.Add(IrrelevantBlocks.ElementAt(idx));
                }
            }
        }


        public List<List<int>> GetAllTuples(List<int> lItems, int idx, int cItems)
        {
            if (cItems == 0)
            {
                List<List<int>> l = new List<List<int>>();
                l.Add(new List<int>());
                return l;
            }

            if (idx == lItems.Count || lItems.Count - idx < cItems)
                return new List<List<int>>();

            List<List<int>> lTuplesWith = GetAllTuples(lItems, idx + 1, cItems - 1);
            List<List<int>> lTuplesWithout = GetAllTuples(lItems, idx + 1, cItems);
            List<List<int>> lAll = new List<List<int>>(lTuplesWithout);

            foreach (List<int> l in lTuplesWith)
            {
                l.Add(lItems[idx]);
                lAll.Add(l);
            }
            return lAll;
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

            for (int i = 0; i <= Reductions; i++)
            {
                List<List<int>> lAllTuples = GetAllTuples(new List<int>(HeavyRelevantBlocks), 0, i + 1);
                foreach (List<int> l in lAllTuples)
                {
                    swProblem.Write("\t(and");
                    foreach (int j in l)
                    {
                        swProblem.Write(" (heavy b" + j + ")");
                    }
                    swProblem.Write(" (CanLiftHeavy n" + i + ")");
                    swProblem.WriteLine(")");
                }
            }


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

            swProblem.WriteLine("\t(CanLiftHeavy n" + Reductions + ")");
            swProblem.WriteLine("");

            swProblem.WriteLine("\t(arm-free)");

            foreach (int iRelevant in HeavyRelevantBlocks)
            {
                swProblem.WriteLine("\t(relevant b" + iRelevant + ")");
            }

            for (int iTower = 0; iTower < InitialTowers.Count; iTower++)
            {
                swProblem.WriteLine("\t(on b" + InitialTowers[iTower][0] + " Table)");
                for (int i = 0; i < InitialTowers[iTower].Count - 1; i++)
                {
                    int iBlock = InitialTowers[iTower][i];
                    int iNextBlock = InitialTowers[iTower][i + 1];
                    swProblem.WriteLine("\t(on b" + iNextBlock + " b" + iBlock + ")");
                }
                swProblem.WriteLine("\t(clear b" + InitialTowers[iTower].Last() + ")");
                swProblem.WriteLine("");
            }


            for (int i = 0; i < HeavyRelevantBlocks.Count; i++)
            {
                if (i < HeavyIrrelvantBlocks.Count)
                {
                    swProblem.WriteLine("\t(oneof (heavy b" + HeavyRelevantBlocks.ElementAt(i) + ") (heavy b" + HeavyIrrelvantBlocks.ElementAt(i) + "))");
                }
                else
                {
                    swProblem.WriteLine("\t(unknown (heavy b" + HeavyRelevantBlocks.ElementAt(i) + "))");
                }
            }


            swProblem.WriteLine(")");

            swProblem.WriteLine("");


            swProblem.WriteLine("   (:goal (and ");
            swProblem.WriteLine("\t(on b" + FinalTower[0] + " Table)");
            for (int i = 0; i < FinalTower.Count - 1; i++)
            {
                int iBlock = FinalTower[i];
                int iNextBlock = FinalTower[i + 1];
                swProblem.WriteLine("\t(on b" + iNextBlock + " b" + iBlock + ")");
            }
            swProblem.WriteLine("\t))");

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
            swDomain.WriteLine("  (:types block count)");

            swDomain.WriteLine("  (:constants");
            swDomain.Write("\tTable ");
            for (int i = 0; i < Size; i++)
            {
                swDomain.Write("b" + i + " ");

            }
            swDomain.WriteLine(" - block");

            for (int i = 0; i <= Reductions; i++)
                swDomain.Write("n" + i + " ");
            swDomain.WriteLine(" - count");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");


            swDomain.WriteLine("    (:predicates 	(CanLiftHeavy ?n - count) (holding ?b - block) (arm-free) (on ?b1 - block ?b2 - block) (clear ?b - block)  (heavy ?b - block)  (relevant ?b - block) ");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action pick-up");
            swDomain.WriteLine("   :parameters (?b - block ?from - block)");
            swDomain.WriteLine("   :precondition (and (arm-free) (on ?b ?from) (clear ?b) (not (heavy ?b)))");
            swDomain.WriteLine("   :effect  (and (not (on ?b ?from)) (holding ?b) (not (clear ?b)) (clear ?from) (not (arm-free)))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action put-down");
            swDomain.WriteLine("   :parameters (?b - block  ?to - block )");
            swDomain.WriteLine("   :precondition (and (holding ?b) (clear ?to))");
            swDomain.WriteLine("   :effect  (and (not (holding ?b)) (arm-free) (on ?b ?to) (clear ?b) (not (clear ?to)))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action ClearTable");
            swDomain.WriteLine("   :precondition (not (clear Table))");
            swDomain.WriteLine("   :effect  (clear Table)");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            /*
            for (int i = 1; i <= HeavyArms; i++)
            {
                swDomain.WriteLine("  (:action pick-up-heavy-" + i);
                swDomain.WriteLine("   :parameters (?b - block ?from - block)");
                swDomain.WriteLine("   :precondition (and (heavy ?b) (CanLiftHeavy n" + i + ") (arm-free) (on ?b ?from) (clear ?b))");
                swDomain.WriteLine("   :effect  (and  (not (CanLiftHeavy n" + i + ")) (CanLiftHeavy n" + (i - 1) + ") (not (on ?b ?from)) (holding ?b) (not (clear ?b)) (clear ?from) (not (arm-free)))");
                swDomain.WriteLine("  )");
                swDomain.WriteLine("");
            }
            */

            for (int i = 1; i <= Reductions; i++)
            {
                swDomain.WriteLine("  (:action reduce-heavy-" + i);
                swDomain.WriteLine("   :parameters (?b - block)");
                swDomain.WriteLine("   :precondition (and (heavy ?b) (relevant ?b) (CanLiftHeavy n" + i + ") (clear ?b))");
                swDomain.WriteLine("   :effect  (and  (not (CanLiftHeavy n" + i + ")) (CanLiftHeavy n" + (i - 1) + ") (not (heavy ?b)))");
                swDomain.WriteLine("  )");
                swDomain.WriteLine("");
            }



            swDomain.WriteLine("  (:action sense-heavy");
            swDomain.WriteLine("   :parameters (?b - block)");
            swDomain.WriteLine("   :precondition (clear ?b)");
            swDomain.WriteLine("   :observe (heavy ?b)");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine(")");

            swDomain.Close();
        }


        public void WriteProblemII(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swProblem = new StreamWriter(sPath + "/p.pddl");
            swProblem.WriteLine("(define (problem " + Name + ")");
            swProblem.WriteLine("  (:domain " + Name + ")");

            swProblem.WriteLine("(:init ");

            swProblem.WriteLine("\t(CanLiftHeavy n" + Reductions + ")");
            swProblem.WriteLine("");

            for (int i = 0; i < Size; i++)
            {
                swProblem.WriteLine("\t(same b" + i + " b" + i + ")");
            }
            swProblem.WriteLine("");

            for (int iTower = 0; iTower < InitialTowers.Count; iTower++)
            {
                swProblem.WriteLine("\t(on b" + InitialTowers[iTower][0] + " Table)");
                for (int i = 0; i < InitialTowers[iTower].Count - 1; i++)
                {
                    int iBlock = InitialTowers[iTower][i];
                    int iNextBlock = InitialTowers[iTower][i + 1];
                    swProblem.WriteLine("\t(on b" + iNextBlock + " b" + iBlock + ")");
                }
                swProblem.WriteLine("\t(clear b" + InitialTowers[iTower].Last() + ")");
                swProblem.WriteLine("");
            }


            for (int i = 0; i < HeavyRelevantBlocks.Count; i++)
            {
                if (i < HeavyIrrelvantBlocks.Count)
                {
                    swProblem.WriteLine("\t(oneof (heavy b" + HeavyRelevantBlocks.ElementAt(i) + ") (heavy b" + HeavyIrrelvantBlocks.ElementAt(i) + "))");
                }
                else
                {
                    swProblem.WriteLine("\t(unknown (heavy b" + HeavyRelevantBlocks.ElementAt(i) + "))");
                }
            }


            swProblem.WriteLine(")");

            swProblem.WriteLine("");


            swProblem.WriteLine("   (:goal (and ");
            swProblem.WriteLine("\t(on b" + FinalTower[0] + " Table)");
            for (int i = 0; i < FinalTower.Count - 1; i++)
            {
                int iBlock = FinalTower[i];
                int iNextBlock = FinalTower[i + 1];
                swProblem.WriteLine("\t(on b" + iNextBlock + " b" + iBlock + ")");
            }
            swProblem.WriteLine("\t))");

            swProblem.WriteLine(")");

            swProblem.Close();
        }

        public void WriteDomainII(string sPath)
        {
            if (!Directory.Exists(sPath))
            {
                Directory.CreateDirectory(sPath);
            }
            StreamWriter swDomain = new StreamWriter(sPath + "/d.pddl");
            swDomain.WriteLine("(define (domain " + Name + ")");
            swDomain.WriteLine("  (:types block count)");

            swDomain.WriteLine("  (:constants");
            swDomain.Write("\tTable ");
            for (int i = 0; i < Size; i++)
            {
                swDomain.Write("b" + i + " ");

            }
            swDomain.WriteLine(" - block");

            for (int i = 0; i <= Reductions; i++)
                swDomain.Write("n" + i + " ");
            swDomain.WriteLine(" - count");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");


            swDomain.WriteLine("    (:predicates 	(CanLiftHeavy ?n - count) (same ?b1 - block ?b2 - block) (on ?b1 - block ?b2 - block) (clear ?b - block)  (heavy ?b - block) ");
            swDomain.WriteLine("    )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action move");
            swDomain.WriteLine("   :parameters (?b - block ?from - block ?to - block )");
            swDomain.WriteLine("   :precondition (and (on ?b ?from) (clear ?b) (clear ?to) (not (heavy ?b)) (not (same ?b ?to)))");
            swDomain.WriteLine("   :effect  (and (not (on ?b ?from)) (on ?b ?to) (clear ?from) (not (clear ?to)))");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine("  (:action ClearTable");
            swDomain.WriteLine("   :precondition (not (clear Table))");
            swDomain.WriteLine("   :effect  (clear Table)");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            for (int i = 1; i <= Reductions; i++)
            {
                swDomain.WriteLine("  (:action move-heavy-" + i);
                swDomain.WriteLine("   :parameters (?b - block ?from - block ?to - block )");
                swDomain.WriteLine("   :precondition (and (heavy ?b) (CanLiftHeavy n" + i + ") (on ?b ?from) (clear ?b) (clear ?to)  (not (same ?b ?to)))");
                swDomain.WriteLine("   :effect  (and  (not (CanLiftHeavy n" + i + ")) (CanLiftHeavy n" + (i - 1) + ") (not (on ?b ?from)) (on ?b ?to) (clear ?from) (not (clear ?to)))");
                swDomain.WriteLine("  )");
                swDomain.WriteLine("");
            }

            swDomain.WriteLine("  (:action sense-heavy");
            swDomain.WriteLine("   :parameters (?b - block)");
            swDomain.WriteLine("   :precondition (clear ?b)");
            swDomain.WriteLine("   :observe (heavy ?b)");
            swDomain.WriteLine("  )");
            swDomain.WriteLine("");

            swDomain.WriteLine(")");

            swDomain.Close();
        }


    }
}
