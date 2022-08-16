using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace CPOR
{
    class MABlocksWorld
    {
        public int Blocks { get; private set; }
        public int Arms { get; private set; }
        public int StacksPerAgent { get; private set; }
        private Stack<int>[] m_aStartState, m_aGoalState;
        public MABlocksWorld(int cBlocks, int cArms, int cStacksPerAgent)
        {
            Blocks = cBlocks;
            Arms = cArms;
            StacksPerAgent = cStacksPerAgent;
            Stack<int>[] a = new Stack<int>[Arms * StacksPerAgent];
            for (int i = 0; i < a.Length; i++)
                a[i] = new Stack<int>();
            for (int i = 0; i < Blocks; i++)
                a[0].Push(i);
            m_aStartState = Shuffle(a, 10000);
            m_aGoalState = Shuffle(m_aStartState, 10000);

        }

        private Stack<int>[] Shuffle(Stack<int>[] a, int cMoves)
        {
            Stack<int>[] aShuffled = new Stack<int>[a.Length];
            for (int i = 0; i < a.Length; i++)
                aShuffled[i] = new Stack<int>(a[i]);

            for (int i = 0; i < cMoves; i++)
            {
                int iStack = RandomGenerator.Next(aShuffled.Length);
                if (aShuffled[iStack].Count == 0)
                    continue;
                int iTargetStack = -1;
                if (iStack == 0 || (iStack < a.Length - 1 && RandomGenerator.NextDouble() < 0.5))
                {
                    iTargetStack = iStack + 1;
                }
                else
                {
                    iTargetStack = iStack - 1;
                }

                int iBlock = aShuffled[iStack].Pop();
                aShuffled[iTargetStack].Push(iBlock);
            }
            return aShuffled;
        }

        public void WriteProblem(string sPathName)
        {
            StreamWriter sw = new StreamWriter(sPathName + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }

        private string GenerateProblem()
        {
            string sProblem = "(define \n";
            sProblem += "(problem MABlocksWorld-" + Arms + "-" + Blocks + "-" + StacksPerAgent + ")\n";
            sProblem += "(:domain MABlocksWorld-" + Arms + "-" + Blocks + "-" + StacksPerAgent + ")\n";
            //sProblem += GenerateObjects() + "\n";
            sProblem += "(:init\n" + ToState(m_aStartState, false) + ")\n";
            sProblem += "(:goal (and\n" + ToState(m_aGoalState, true) + "))\n";
            sProblem += ")";
            return sProblem;
        }

        private string ToState(Stack<int>[] a, bool bGoalState)
        {
            string sState = "";// "(and\n";
            for (int iStack = 0; iStack < a.Length; iStack++)
            {
                List<int> lStack = a[iStack].ToList();
                if (!bGoalState)
                {
                    //sState += "\t(in-stack T" + iStack + " S" + iStack + ")\n";
                    if (lStack.Count == 0)
                        sState += "\t(clear T" + iStack + " S" + iStack + ")\n";
                }
                for (int i = 0; i < a[iStack].Count; i++)
                {
                    int iBlock = lStack[i];
                    //sState += "\t(in-stack B" + iBlock + " S" + iStack + ")\n";
                    if (i == 0)
                    {
                        sState += "\t(on B" + iBlock + " T" + iStack + " S" + iStack + ")\n";
                    }
                    else
                    {
                        sState += "\t(on B" + iBlock + " B" + lStack[i - 1] + " S" + iStack + ")\n";
                    }
                    if (i == a[iStack].Count - 1)
                    {
                        sState += "\t(clear B" + iBlock + " S" + iStack + ")\n";
                    }
                }

            }
            //sState += ")";
            return sState;
        }


        private string GenerateConstants()
        {
            int iBlock = 0, iArm = 0;
            string sObjects = "(:constants\n";
            for (iBlock = 0; iBlock < Blocks; iBlock++)
            {
                sObjects += "\t B" + iBlock + " - BLOCK\n";
            }
            for (int i = 0; i < Arms * StacksPerAgent + 1; i++)
            {
                sObjects += "\t T" + i + " - BLOCK\n";
            }
            //sObjects += "\t T - BLOCK\n";
            for (iArm = 0; iArm < Arms; iArm++)
            {
                sObjects += "\t A" + iArm + " - ARM\n";
            }
            for (int i = 0; i < Arms * StacksPerAgent + 1; i++)
            {
                sObjects += "\t S" + i + " - STACK\n";
            }
            sObjects += ")";
            return sObjects;
        }

        private string GeneratePredicates()
        {
            string sPredicates = "(:predicates\n";
            sPredicates += "\t(on ?b1 - BLOCK ?b2 - BLOCK ?s - STACK)\n";
            //sPredicates += "\t(in-stack ?b - BLOCK ?s - STACK)\n";
            sPredicates += "\t(clear ?b - BLOCK ?s - STACK)\n";
            sPredicates += ")\n";
            return sPredicates;
        }


        private string GenerateActions()
        {
            string sActions = "";
            for (int iArm = 0; iArm < Arms; iArm++)
            {
                for (int iStack = 0; iStack < StacksPerAgent; iStack++)
                {
                    sActions += GenerateMove(iArm, iArm * StacksPerAgent + iStack, iArm * StacksPerAgent + iStack + 1) + "\n";
                    sActions += GenerateMove(iArm, iArm * StacksPerAgent + iStack + 1, iArm * StacksPerAgent + iStack) + "\n";
                }
            }
            return sActions;
        }

        private string GenerateMove(int iArm, int iSourceStack, int iTargetStack)
        {
            string sAction = "(:action move-a" + iArm + "-s" + iSourceStack + "-s" + iTargetStack + "\n";
            sAction += ":parameters (?bMove - BLOCK ?bSource - BLOCK ?bTarget - BLOCK)\n";
            sAction += ":precondition (and (on ?bMove ?bSource S" + iSourceStack + ") (clear ?bMove S" + iSourceStack + ") (clear ?bTarget S" + iTargetStack + ") )\n";
            sAction += ":effect (and (not (on ?bMove ?bSource S" + iSourceStack + ")) (on ?bMove ?bTarget S" + iTargetStack + ") (clear ?bSource S" + iSourceStack + ") (not (clear ?bTarget S" + iTargetStack + ")) (not (clear ?bMove S" + iSourceStack + ")) (clear ?bMove S" + iTargetStack + "))\n";
            sAction += ")\n";
            return sAction;
        }
        /*
        private string GenerateMove(int iArm, int iSourceStack, int iTargetStack)
        {
            string sAction = "(:action move-a" + iArm + "-s" + iSourceStack + "-s" + iTargetStack + "\n";
            sAction += ":parameters (?bMove - BLOCK ?bSource - BLOCK ?bTarget - BLOCK)\n";
            sAction += ":precondition (and (on ?bMove ?bSource S" + iSourceStack + ") (in-stack ?bMove S" + iSourceStack + ") (clear ?bMove S" + iSourceStack + ") (clear ?bTarget S" + iTargetStack + ") (in-stack ?bTarget S" + iTargetStack + ") )\n";
            sAction += ":effect (and (not (on ?bMove ?bSource S" + iSourceStack + ")) (on ?bMove ?bTarget S" + iTargetStack + ") (not (in-stack ?bMove S" + iSourceStack + ")) (in-stack ?bMove S" + iTargetStack + ") (clear ?bSource S" + iSourceStack + ") (not (clear ?bTarget S" + iTargetStack + ")) (not (clear ?bMove S" + iSourceStack + ")) (clear ?bMove S" + iTargetStack + "))\n";
            sAction += ")\n";
            return sAction;
        }
         * */

        /*
        private string GenerateMove(int iArm, int iSourceStack, int iTargetStack)
        {
            string sAction = "(:action move-a" + iArm + "-s" + iSourceStack + "-s" + iTargetStack + "\n";
            sAction += ":parameters (?bMove - BLOCK)\n";
            sAction += ":precondition (and (in-stack ?bMove S" + iSourceStack + ") (clear ?bMove))\n";
            sAction += ":effect (and (not (in-stack ?bMove S" + iSourceStack + ")) (in-stack ?bMove S" + iTargetStack + ")\n";
            for (int iBlock = 0; iBlock < Blocks; iBlock++)
            {
                sAction += "\t(when (on ?bMove B" + iBlock + ") (and (not (on ?bMove B" + iBlock + ")) (clear B" + iBlock + ")))\n";
                sAction += "\t(when (and (in-stack B" + iBlock + " S" + iTargetStack + ") (clear B" + iBlock + ")) (and (on ?bMove B" + iBlock + ") (not (clear B" + iBlock + "))))\n";
            }
            sAction += "\t)\n";
            sAction += ")\n";
            return sAction;
        }
        */

        public void WriteDomain(string sPath)
        {
            DirectoryInfo di = new DirectoryInfo(sPath);
            if (!di.Exists)
                di.Create();
            StreamWriter sw = new StreamWriter(sPath + @"\d.pddl");
            sw.Write(GenerateDomain());
            sw.Close();
        }

        private string GenerateDomain()
        {
            string sDomain = "(define \n";
            sDomain += "(domain MABlocksWorld-" + Arms + "-" + Blocks + "-" + StacksPerAgent + ")\n";
            sDomain += "(:types PEG COLOR VALUE GUESSSTEP)\n";
            sDomain += GenerateConstants();
            sDomain += GeneratePredicates();
            sDomain += GenerateActions();
            sDomain += ")";
            return sDomain;
        }


        public string Name { get { return "MABlocksWorld-" + Arms + "-" + Blocks + "-" + StacksPerAgent; } }
    }
}