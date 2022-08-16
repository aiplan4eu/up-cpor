using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;

namespace CPOR
{
    class RockSample
    {
        public int Size { get; private set; }
        public int Rocks { get; private set; }

        private bool m_bAllowSensing = true;
        private bool m_bTwoStageAntena = true;

        private int m_cMoveSteps;

        public RockSample(int iSize, int cRocks, int cMoveSteps)
        {
            Size = iSize;
            Rocks = cRocks;
            m_cMoveSteps = cMoveSteps;
            PrintMap();
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
            sProblem += "(problem " + Name + ")\n";
            sProblem += "(:domain " + Name + ")\n";
            //sProblem += GenerateObjects() + "\n";
            sProblem += GetInitState() + "\n";
            sProblem += GetGoalState() + "\n";
            sProblem += ")";
            return sProblem;
        }

        private string GetGoalState()
        {
            string sGoal = "(:goal (and";
            for (int iRock = 0; iRock < Rocks; iRock++)
                sGoal += " (not (good r" + iRock + "))";
            sGoal += "))";
            return sGoal;
        }

        private string GenerateObjects()
        {

            string sObjects = "(:objects\n";

            return sObjects;
        }

        private int MaxHeight
        {
            get
            {
                if (!m_bTwoStageAntena)
                    return Size / 2;
                return 1;
            }
        }

        private string GenerateConstants()
        {
            int iX = 0, iY = 0, iRock = 0, iHeight = 0;
            string sObjects = "(:constants\n";
            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {
                    sObjects += "\t p" + iX + "-" + iY + " - LOCATION\n";
                }
            }
            for (iRock = 0; iRock < Rocks; iRock++)
            {
                sObjects += "\t r" + iRock + " - ROCK\n";
            }
            if (m_bAllowSensing)
            {
                for (iHeight = 0; iHeight <= MaxHeight; iHeight++)
                {
                    sObjects += "\t h" + iHeight + " - HEIGHT\n";
                }
            }
            if (m_cMoveSteps > 1)
            {
                for (int iMoveStep = 0; iMoveStep < m_cMoveSteps; iMoveStep++)
                {
                    sObjects += "\t ms" + iMoveStep + " - MOVESTEP\n";
                }
            }
            /*
            for (iX = 0; iX <= Size; iX++)
            {
                sObjects += "\t v" + iX + " - VALUE\n";
            }
             * */
            sObjects += ")";
            return sObjects;
        }

        private int[,] GetRockLocations()
        {
            Random r = new Random(2);
            int[,] aRocks = new int[Rocks, 2];
            for (int iRock = 0; iRock < Rocks; iRock++)
            {
                bool bUsed = true;
                while (bUsed)
                {
                    bUsed = false;
                    aRocks[iRock, 0] = r.Next(Size) + 1;
                    aRocks[iRock, 1] = r.Next(Size) + 1;
                    for (int iPreviousRock = 0; iPreviousRock < iRock; iPreviousRock++)
                    {
                        if (aRocks[iRock, 0] == aRocks[iPreviousRock, 0] && aRocks[iRock, 1] == aRocks[iPreviousRock, 1])
                            bUsed = true;
                    }
                }
            }
            return aRocks;
        }

        private void PrintMap()
        {
            int iX = 0, iY = 0;
            int[,] aiRocks = GetRockLocations();
            int[,] abMap = new int[Size, Size];
            for (int iRock = 0; iRock < Rocks; iRock++)
            {
                iX = aiRocks[iRock, 0];
                iY = aiRocks[iRock, 1];
                abMap[iX - 1, iY - 1] = iRock + 1;
            }
            for (iX = 0; iX < Size; iX++)
            {
                for (iY = 0; iY < Size; iY++)
                {
                    if (abMap[iX, iY] == 0)
                        Debug.Write("X");
                    else
                        Debug.Write(abMap[iX, iY] + "");
                }
                Debug.WriteLine("");
            }
        }


        private string GetInitState()
        {
            int iRock = 0;
            int iX = 0, iY = 0, iOtherX = 0, iOtherY = 0;
            int[,] aRocks = GetRockLocations();
            string sInit = "(:init\n";
            sInit += "(and\n";
            /*
            int iMiddle = Size / 2 + 1;
            sInit += "\t(agent-at p" + iMiddle + "-" + iMiddle + ")\n";
             * */
            sInit += "\t(agent-at p" + 1 + "-" + 1 + ")\n";
            for (iRock = 0; iRock < Rocks; iRock++)
            {
                sInit += "\t(rock-at r" + iRock + "  p" + aRocks[iRock, 0] + "-" + aRocks[iRock, 1] + ")\n";
                sInit += "\t(oneof (good r" + iRock + ") (not (good r" + iRock + ")))\n";
            }
            if (m_bAllowSensing)
                sInit += "\t(antena-height h0)\n";
            if (m_cMoveSteps > 0)
                sInit += "(move-step ms0)\n";

            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {
                    for (iOtherX = 1; iOtherX <= Size; iOtherX++)
                    {
                        for (iOtherY = 1; iOtherY <= Size; iOtherY++)
                        {
                            double dDistance = GetDistance(iX, iY, iOtherX, iOtherY);
                            if (dDistance <= 1 && dDistance > 0)
                                sInit += "\t(adj p" + iX + "-" + iY + " p" + iOtherX + "-" + iOtherY + ")\n";
                            //sInit += "\t(distance p" + iX + "-" + iY + " p" + iOtherX + "-" + iOtherY + " v" + iDistance + ")\n";
                        }
                    }
                }
            }

            sInit += ")\n)\n";
            return sInit;
        }

        private string GeneratePredicates()
        {
            string sPredicates = "(:predicates\n";
            sPredicates += "\t(rock-at ?r - ROCK ?p - LOCATION)\n";
            sPredicates += "\t(agent-at ?p - LOCATION)\n";
            sPredicates += "\t(adj ?p1 - LOCATION ?p2 - LOCATION)\n";
            sPredicates += "\t(good ?r - ROCK)\n";
            if (m_bAllowSensing)
            {
                sPredicates += "\t(antena-height ?h - HEIGHT)\n";
                sPredicates += "\t(good-rocks-in-range)\n";
            }
            if (m_cMoveSteps > 0)
            {
                sPredicates += "(move-step ?m - MOVESTEP)\n";
                sPredicates += "(move-target ?p - LOCATION)\n";
            }
            //sPredicates += "\t(distance ?p1 - LOCATION ?p2 - LOCATION ?v - VALUE)\n";
            sPredicates += ")\n";
            return sPredicates;
        }


        private string GenerateActions()
        {
            string sActions = "";
            sActions += GenerateMoveAction() + "\n";
            sActions += GenerateSampleAction() + "\n";
            if (m_bAllowSensing)
            {
                sActions += GenerateRaiseAntenaAction() + "\n";
                sActions += GenerateLowerAntenaAction() + "\n";
                sActions += GenerateActivateSensorActions() + "\n";
                sActions += GenerateObservationAction() + "\n";
            }
            return sActions;
        }

        private void GenerateActions(StreamWriter sw)
        {
            sw.Write(GenerateMoveAction() + "\n");
            sw.Write(GenerateSampleAction() + "\n");
            if (m_bAllowSensing)
            {
                sw.Write(GenerateRaiseAntenaAction() + "\n");
                sw.Write(GenerateLowerAntenaAction() + "\n");
                foreach (string sAction in GenerateActivateSensorActions())
                    sw.Write(sAction + "\n");
                sw.Write(GenerateObservationAction() + "\n");
            }
        }

        private string GenerateMoveAction()
        {
            string sAction = "";
            if (m_cMoveSteps > 1)
            {
                if (m_bAllowSensing)
                {
                    for (int iMoveStep = 0; iMoveStep < m_cMoveSteps - 1; iMoveStep++)
                    {
                        sAction += "(:action move" + iMoveStep + "\n";
                        sAction += ":parameters (?pSource - LOCATION ?pTarget - LOCATION)\n";
                        if (iMoveStep == 0)
                        {
                            sAction += ":precondition (and (agent-at ?pSource) (adj ?pSource ?pTarget) (antena-height h0) (move-step ms" + iMoveStep + "))\n";
                            sAction += ":effect (and (move-target ?pTarget) (not (move-step ms" + iMoveStep + ")) (move-step ms" + (iMoveStep + 1) + ") (not (good-rocks-in-range))))\n";
                        }
                        else
                        {
                            sAction += ":precondition (and (agent-at ?pSource) (adj ?pSource ?pTarget) (move-target ?pTarget) (antena-height h0) (move-step ms" + iMoveStep + "))\n";
                            sAction += ":effect (and (not (move-step ms" + iMoveStep + ")) (move-step ms" + (iMoveStep + 1) + ") (not (good-rocks-in-range))))\n";
                        }
                    }
                    sAction += "(:action move" + (m_cMoveSteps - 1) + "\n";
                    sAction += ":parameters (?pSource - LOCATION ?pTarget - LOCATION)\n";
                    sAction += ":precondition (and (agent-at ?pSource) (adj ?pSource ?pTarget) (move-target ?pTarget) (antena-height h0) (move-step ms" + (m_cMoveSteps - 1) + "))\n";
                    sAction += ":effect (and  (not (move-step ms" + (m_cMoveSteps - 1) + ")) (move-step ms0) (not (good-rocks-in-range))";
                    sAction += "(not (agent-at ?pSource)) (agent-at ?pTarget) (not (move-target ?pTarget))";
                    sAction += "))\n";
                }
                else
                {
                    sAction += ":precondition (and (agent-at ?pSource) (adj ?pSource ?pTarget))\n";
                    sAction += ":effect (and (agent-at ?pTarget) (not (agent-at ?pSource))))\n";
                }
            }
            else
            {
                sAction = "(:action move\n";
                sAction += ":parameters (?pSource - LOCATION ?pTarget - LOCATION)\n";
                if (m_bAllowSensing)
                {
                    sAction += ":precondition (and (agent-at ?pSource) (adj ?pSource ?pTarget) (antena-height h0))\n";
                    sAction += ":effect (and (agent-at ?pTarget) (not (agent-at ?pSource)) (not (good-rocks-in-range))))\n";
                }
                else
                {
                    sAction += ":precondition (and (agent-at ?pSource) (adj ?pSource ?pTarget))\n";
                    sAction += ":effect (and (agent-at ?pTarget) (not (agent-at ?pSource))))\n";
                }
            }

            return sAction;
        }
        private string GenerateSampleAction()
        {
            string sAction = "(:action sample\n";
            sAction += ":parameters (?r - ROCK ?p - LOCATION)\n";
            if (m_bAllowSensing)
                sAction += ":precondition (and (agent-at ?p) (rock-at ?r ?p) (good ?r))\n";
            else
                sAction += ":precondition (and (agent-at ?p) (rock-at ?r ?p))\n";
            sAction += ":effect (not (good ?r)))\n";

            return sAction;
        }
        private string GenerateRaiseAntenaAction()
        {
            string sAction = "(:action raise-antena\n";

            //sAction += ":precondition \n";
            sAction += ":effect (and\n";
            //adding this forces us to give all things in the tags
            //sAction += "\t(not (good-rocks-in-range))\n";
            if (m_bTwoStageAntena)
            {
                sAction += "(antena-height h" + MaxHeight + ")";
                sAction += "(not (antena-height h0))";
            }
            else
            {
                for (int iHeight = 0; iHeight < MaxHeight; iHeight++)
                {
                    sAction += "\t(when (antena-height h" + iHeight + ") (and (not (antena-height h" + iHeight + ")) (antena-height h" + (iHeight + 1) + ")))\n";
                }
            }
            sAction += "))\n";
            return sAction;
        }
        private string GenerateLowerAntenaAction()
        {
            string sAction = "(:action lower-antena\n";

            //sAction += ":precondition \n";
            sAction += ":effect (and\n";
            //adding this forces us to give all things in the tags
            //sAction += "\t(not (good-rocks-in-range))\n";
            if (m_bTwoStageAntena)
            {
                sAction += "(not (antena-height h" + MaxHeight + "))";
                sAction += "(antena-height h0)";
            }
            else
            {
                for (int iHeight = 0; iHeight < MaxHeight; iHeight++)
                {
                    sAction += "\t(when (antena-height h" + (iHeight + 1) + ") (and (not (antena-height h" + (iHeight + 1) + ")) (antena-height h" + iHeight + ")))\n";
                }
            }
            sAction += "))\n";
            return sAction;
        }
        private double GetDistance(int iX, int iY, int iOtherX, int iOtherY)
        {
            int iDeltaX = iX - iOtherX, iDeltaY = iY - iOtherY;
            return Math.Sqrt(iDeltaX * iDeltaX + iDeltaY * iDeltaY);
        }
        private List<int> GetRocksInRange(int iX, int iY, int iRange)
        {
            List<int> lRocks = new List<int>();
            int[,] aiRockLocations = GetRockLocations();
            for (int iRock = 0; iRock < Rocks; iRock++)
            {
                if (GetDistance(iX, iY, aiRockLocations[iRock, 0], aiRockLocations[iRock, 1]) <= iRange)
                    lRocks.Add(iRock);
            }
            return lRocks;
        }
        private string GenerateActivateSensorAction()
        {
            string sAction = "(:action activate-sensor\n";
            //sAction += ":precondition (not (good-rocks-in-range))\n";
            sAction += ":effect (and\n";
            for (int iX = 1; iX <= Size; iX++)
            {
                for (int iY = 1; iY <= Size; iY++)
                {
                    for (int iHeight = 0; iHeight <= MaxHeight; iHeight++)
                    {
                        if (!m_bTwoStageAntena || iHeight == 0 || iHeight == MaxHeight)
                        {

                            List<int> lRocksInRange = GetRocksInRange(iX, iY, iHeight);
                            if (lRocksInRange.Count > 0)
                            {
                                sAction += "\t(when (and (antena-height h" + iHeight + ")";
                                sAction += " (agent-at p" + iX + "-" + iY + ")";
                                sAction += " (or";
                                foreach (int iRock in lRocksInRange)
                                {
                                    sAction += " (good r" + iRock + ")";
                                }

                                sAction += ")) (good-rocks-in-range))\n";

                                sAction += "\t(when (and (antena-height h" + iHeight + ")";
                                sAction += " (agent-at p" + iX + "-" + iY + ")";
                                sAction += " (and";
                                foreach (int iRock in lRocksInRange)
                                {
                                    sAction += " (not (good r" + iRock + "))";
                                }

                                sAction += ")) (not (good-rocks-in-range)))\n";
                            }
                        }
                    }
                }
            }
            sAction += "))\n";
            return sAction;
        }

        //action per location and antena height
        private List<string> GenerateActivateSensorActions()
        {
            List<string> lActions = new List<string>();
            for (int iX = 1; iX <= Size; iX++)
            {
                for (int iY = 1; iY <= Size; iY++)
                {
                    for (int iHeight = 0; iHeight <= MaxHeight; iHeight++)
                    {
                        if (!m_bTwoStageAntena || iHeight == 0 || iHeight == MaxHeight)
                        {
                            List<int> lRocksInRange = GetRocksInRange(iX, iY, iHeight);
                            if (lRocksInRange.Count > 0)
                            {
                                string sAction = "(:action activate-sensor-at-p" + iX + "-" + iY + "-h" + iHeight + "\n";
                                sAction += ":precondition (and (agent-at p" + iX + "-" + iY + ") (antena-height h" + iHeight + "))\n";
                                sAction += ":effect (and\n";
                                sAction += "\t(when (or ";
                                foreach (int iRock in lRocksInRange)
                                {
                                    sAction += " (good r" + iRock + ")";
                                }

                                sAction += ") (good-rocks-in-range))\n";

                                sAction += "\t(when (and ";
                                foreach (int iRock in lRocksInRange)
                                {
                                    sAction += " (not (good r" + iRock + "))";
                                }

                                sAction += ") (not (good-rocks-in-range)))\n";
                                sAction += "))\n";
                                lActions.Add(sAction);
                            }
                        }
                    }
                }
            }
            return lActions;
        }

        //action per location
        private List<string> GenerateActivateSensorActionsII()
        {
            List<string> lActions = new List<string>();
            for (int iX = 1; iX <= Size; iX++)
            {
                for (int iY = 1; iY <= Size; iY++)
                {
                    string sAction = "(:action activate-sensor-at-p" + iX + "-" + iY + "\n";
                    sAction += ":precondition (agent-at p" + iX + "-" + iY + ")\n";
                    sAction += ":effect (and\n";
                    for (int iHeight = 0; iHeight <= MaxHeight; iHeight++)
                    {
                        List<int> lRocksInRange = GetRocksInRange(iX, iY, iHeight);
                        if (lRocksInRange.Count > 0)
                        {
                            sAction += "\t(when (and (antena-height h" + iHeight + ")";
                            sAction += " (or";
                            foreach (int iRock in lRocksInRange)
                            {
                                sAction += " (good r" + iRock + ")";
                            }

                            sAction += ")) (good-rocks-in-range))\n";

                            sAction += "\t(when (and (antena-height h" + iHeight + ")";
                            foreach (int iRock in lRocksInRange)
                            {
                                sAction += " (not (good r" + iRock + "))";
                            }

                            sAction += ") (not (good-rocks-in-range)))\n";
                        }
                    }
                    sAction += "))\n";
                    lActions.Add(sAction);
                }
            }
            return lActions;
        }

        private string GenerateObservationAction()
        {
            string sAction = "(:action observe-sensor\n";
            sAction += ":observe (good-rocks-in-range))\n";
            /*
            sAction += "(:action observe-antena-height\n";
            sAction += ":parameters (?h - HEIGHT)\n";
            sAction += ":observe (antena-height ?h))\n";
             * */
            return sAction;

        }

        public void WriteDomain(string sPath)
        {
            if (!Directory.Exists(sPath))
                Directory.CreateDirectory(sPath);
            StreamWriter sw = new StreamWriter(sPath + @"\d.pddl");
            //sw.Write(GenerateDomain());
            GenerateDomain(sw);
            sw.Close();
        }

        private string GenerateDomain()
        {
            string sDomain = "(define \n";
            sDomain += "(domain " + Name + ")\n";
            sDomain += "(:types LOCATION ROCK HEIGHT MOVESTEP)\n";
            sDomain += GenerateConstants() + "\n";
            sDomain += GeneratePredicates();
            sDomain += GenerateActions();
            sDomain += ")";
            return sDomain;
        }
        private void GenerateDomain(StreamWriter sw)
        {
            sw.Write("(define \n");
            sw.Write("(domain " + Name + ")\n");
            sw.Write("(:types LOCATION ROCK HEIGHT MOVESTEP)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }






        public string Name { get { return "RockSample" + Size + "-" + Rocks; } }


        public static List<string> RockSampleHeuristic(PartiallySpecifiedState pssCurrent, Domain domain)
        {
            List<string> lActions = new List<string>();
            int iX = -1, iY = 1;
            int iSize = 0;
            foreach (GroundedPredicate p in pssCurrent.Observed)
            {
                if (p.Name.Contains("agent-at"))
                {
                    string[] a = p.Constants[0].Name.Substring(1).Split('-');
                    if (!p.Negation)
                    {
                        iX = int.Parse(a[0]);
                        iY = int.Parse(a[1]);
                    }
                    if (int.Parse(a[0]) > iSize)
                        iSize = int.Parse(a[0]);
                }
            }

            int iXNew = iX, iYNew = iY;

            if (iX < iSize - 1 && iY % 2 == 1)
                iXNew++;
            else if (iX > 1 && iY % 2 == 0)
                iXNew--;
            else
            {
                iYNew++;
            }
            lActions.Add("move p" + iX + "-" + iY + " p" + iXNew + "-" + iYNew);
            bool bValidSensorH1 = false;
            bool bValidSensorH0 = false;
            foreach (Action a in domain.Actions)
            {
                if (a.Name == "activate-sensor-at-p" + iXNew + "-" + iYNew + "-h1")
                    bValidSensorH1 = true;
                if (a.Name == "activate-sensor-at-p" + iXNew + "-" + iYNew + "-h0")
                    bValidSensorH0 = true;

            }
            if (bValidSensorH1)
            {
                lActions.Add("raise-antena");
                lActions.Add("activate-sensor-at-p" + iXNew + "-" + iYNew + "-h1");
                lActions.Add("observe-sensor");
                lActions.Add("lower-antena");
            }
            if (bValidSensorH0)
            {
                lActions.Add("activate-sensor-at-p" + iXNew + "-" + iYNew + "-h0");
                lActions.Add("observe-sensor");
            }
            return lActions;
        }
    }
}
