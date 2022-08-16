using System;
using System.IO;

namespace CPOR
{
    class CatchtInvaders
    {
        public int Size { get; private set; }
        public int Invaders { get; private set; }

        public CatchtInvaders(int iSize, int cInvaders)
        {
            Size = iSize;
            Invaders = cInvaders;
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
            for (int iInvader = 0; iInvader < Invaders; iInvader++)
                sGoal += " (caught i" + iInvader + ")";
            sGoal += "))";
            return sGoal;
        }

        private string GenerateConstants()
        {
            int iX = 0, iY = 0, iInvader = 0;
            string sObjects = "(:constants\n";
            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {
                    sObjects += "\t p" + iX + "-" + iY + " - LOCATION\n";
                }
            }
            for (iInvader = 0; iInvader < Invaders; iInvader++)
            {
                sObjects += "\t i" + iInvader + " - INVADER\n";
            }
            sObjects += ")";
            return sObjects;
        }

        private string GetInitState()
        {
            int iInvader = 0;
            int iX = 0, iY = 0, iOtherX = 0, iOtherY = 0;
            string sInit = "(:init\n";
            sInit += "(and\n";
            int iMiddle = Size / 2 + 1;
            sInit += "\t(agent-at p" + iMiddle + "-" + iMiddle + ")\n";
            sInit += "\t(agent-on-ground)\n";
            for (iInvader = 0; iInvader < Invaders; iInvader++)
            {
                sInit += "\t(oneof";
                for (iX = 1; iX <= Size; iX++)
                    for (iY = 1; iY <= Size; iY++)
                        sInit += " (invader-at i" + iInvader + "  p" + iX + "-" + iY + ")\n";
                sInit += ")\n";
            }

            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {
                    for (iOtherX = 1; iOtherX <= Size; iOtherX++)
                    {
                        for (iOtherY = 1; iOtherY <= Size; iOtherY++)
                        {
                            if (GetDistance(iX, iY, iOtherX, iOtherY) == 1)
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
            sPredicates += "\t(invader-at ?i - INVADER ?p - LOCATION)\n";
            sPredicates += "\t(agent-at ?p - LOCATION)\n";
            sPredicates += "\t(adj ?p1 - LOCATION ?p2 - LOCATION)\n";
            sPredicates += "\t(agent-on-tree)\n";
            sPredicates += "\t(agent-on-ground)\n";
            sPredicates += "\t(caught ?i - INVADER)\n";
            sPredicates += "\t(noise)\n";
            sPredicates += "\t(sight)\n";
            sPredicates += "\t(sight-at ?p - LOCATION)\n";
            sPredicates += ")\n";
            return sPredicates;
        }


        private string GenerateActions()
        {
            string sActions = "";
            sActions += GenerateMoveAction() + "\n";
            sActions += GenerateClimbActions() + "\n";
            sActions += GenerateWatchOnGroundAction() + "\n";
            sActions += GenerateWatchOnTreeAction() + "\n";
            sActions += GenerateListenAction() + "\n";
            sActions += GenerateObservationActions() + "\n";
            sActions += GenerateCatchAction() + "\n";
            return sActions;
        }

        private string GenerateClimbActions()
        {
            string sActions = "(:action climb-up\n";
            sActions += ":precondition (agent-on-ground)\n";
            sActions += ":effect (and (not (agent-on-ground)) (agent-on-tree)))\n";
            sActions += "(:action climb-down\n";
            sActions += ":precondition (agent-on-tree)\n";
            sActions += ":effect (and (not (agent-on-tree)) (agent-on-ground)))\n";
            return sActions;
        }


        private string GenerateListenAction()
        {
            int iX = 0, iY = 0, iOtherX = 0, iOtherY = 0;
            string sAction = "(:action listen\n";
            sAction += ":effect (and\n";
            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {

                    for (int iInvader = 0; iInvader < Invaders; iInvader++)
                    {
                        for (iOtherX = 1; iOtherX <= Size; iOtherX++)
                        {
                            for (iOtherY = 1; iOtherY <= Size; iOtherY++)
                            {
                                if (GetDistance(iX, iY, iOtherX, iOtherY) <= 3)
                                {
                                    sAction += "\t(when (and (agent-at p" + iX + "-" + iY + ")";
                                    sAction += " (invader-at i" + iInvader + " p" + iOtherX + "-" + iOtherY + ")) (noise))\n";
                                }
                            }
                        }
                    }

                }
            }
            sAction += "))\n";
            return sAction;
        }

        private string GenerateWatchOnGroundAction()
        {
            int iX = 0, iY = 0, iOtherX = 0, iOtherY = 0;
            string sAction = "(:action watch-on-ground\n";
            sAction += ":precondition (agent-on-ground)\n";
            sAction += ":effect (and\n";
            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {
                    for (iOtherX = 1; iOtherX <= Size; iOtherX++)
                    {
                        for (iOtherY = 1; iOtherY <= Size; iOtherY++)
                        {
                            if (GetDistance(iX, iY, iOtherX, iOtherY) <= 1)
                            {

                                for (int iInvader = 0; iInvader < Invaders; iInvader++)
                                {
                                    sAction += "\t(when (and (agent-at p" + iX + "-" + iY + ") ";
                                    sAction += " (invader-at i" + iInvader + " p" + iOtherX + "-" + iOtherY + "))";
                                    sAction += " (and (sight-at p" + iOtherX + "-" + iOtherY + ") (sight)))\n";
                                }

                            }
                        }
                    }
                }
            }
            sAction += "))\n";
            return sAction;
        }

        private string GenerateWatchOnTreeAction()
        {
            int iX = 0, iY = 0, iOtherX = 0, iOtherY = 0;
            string sAction = "(:action watch-on-tree\n";
            sAction += ":precondition (agent-on-tree)\n";
            sAction += ":effect (and\n";
            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {
                    for (iOtherX = 1; iOtherX <= Size; iOtherX++)
                    {
                        for (iOtherY = 1; iOtherY <= Size; iOtherY++)
                        {
                            if (GetDistance(iX, iY, iOtherX, iOtherY) <= 4)
                            {

                                for (int iInvader = 0; iInvader < Invaders; iInvader++)
                                {
                                    sAction += "\t(when (and (agent-at p" + iX + "-" + iY + ")";
                                    sAction += " (invader-at i" + iInvader + " p" + iOtherX + "-" + iOtherY + "))";
                                    sAction += " (and (sight-at p" + iOtherX + "-" + iOtherY + ") (sight)))\n";
                                }

                            }
                        }
                    }
                }
            }
            sAction += "))\n";
            return sAction;
        }

        /*
        private string GenerateListenAction()
        {
            int iX = 0, iY = 0, iOtherX = 0, iOtherY = 0;
            string sAction = "(:action listen\n";
            sAction += ":effect (and\n";
            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {
                    sAction += "\t(when (and (agent-at p" + iX + "-" + iY + ") (or ";
                    for (int iInvader = 0; iInvader < Invaders; iInvader++)
                    {
                        for (iOtherX = 1; iOtherX <= Size; iOtherX++)
                        {
                            for (iOtherY = 1; iOtherY <= Size; iOtherY++)
                            {
                                if (GetDistance(iX, iY, iOtherX, iOtherY) <= 3)
                                {
                                    sAction += " (invader-at i" + iInvader + " p" + iOtherX + "-" + iOtherY + ")";
                                }
                            }
                        }
                    }
                    sAction += ")) (noise))\n";
                }
            }
            sAction += "))\n";
            return sAction;
        }


        private string GenerateWatchOnGroundAction()
        {
            int iX = 0, iY = 0, iOtherX = 0, iOtherY = 0;
            string sAction = "(:action watch-on-ground\n";
            sAction += ":precondition (agent-on-ground)\n";
            sAction += ":effect (and\n";
            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {
                    for (iOtherX = 1; iOtherX <= Size; iOtherX++)
                    {
                        for (iOtherY = 1; iOtherY <= Size; iOtherY++)
                        {
                            if (GetDistance(iX, iY, iOtherX, iOtherY) <= 1)
                            {
                                sAction += "\t(when (and (agent-at p" + iX + "-" + iY + ") (or ";
                                for (int iInvader = 0; iInvader < Invaders; iInvader++)
                                {
                                    sAction += " (invader-at i" + iInvader + " p" + iOtherX + "-" + iOtherY + ")";
                                }
                                sAction += ")) (and (sight-at p" + iOtherX + "-" + iOtherY + ") (sight)))\n";
                            }
                        }
                    }
                }
            }
            sAction += "))\n";
            return sAction;
        }
        private string GenerateWatchOnTreeAction()
        {
            int iX = 0, iY = 0, iOtherX = 0, iOtherY = 0;
            string sAction = "(:action watch-on-tree\n";
            sAction += ":precondition (agent-on-tree)\n";
            sAction += ":effect (and\n";
            for (iX = 1; iX <= Size; iX++)
            {
                for (iY = 1; iY <= Size; iY++)
                {
                    for (iOtherX = 1; iOtherX <= Size; iOtherX++)
                    {
                        for (iOtherY = 1; iOtherY <= Size; iOtherY++)
                        {
                            if (GetDistance(iX, iY, iOtherX, iOtherY) <= 4)
                            {
                                sAction += "\t(when (and (agent-at p" + iX + "-" + iY + ") (or ";
                                for (int iInvader = 0; iInvader < Invaders; iInvader++)
                                {
                                    sAction += " (invader-at i" + iInvader + " p" + iOtherX + "-" + iOtherY + ")";
                                }
                                sAction += ")) (and (sight-at p" + iOtherX + "-" + iOtherY + ") (sight)))\n";
                            }
                        }
                    }
                }
            }
            sAction += "))\n";
            return sAction;
        }
*/

        private string GenerateCatchAction()
        {
            string sAction = "(:action catch-invader\n";
            sAction += ":parameters (?p - LOCATION ?i - INVADER)\n";
            sAction += ":precondition (and (agent-at ?p) (invader-at ?i ?p))\n";
            sAction += ":effect (caught ?i))\n";
            return sAction;
        }

        private string GenerateMoveAction()
        {
            int iX = 0, iY = 0, iOtherX = 0, iOtherY = 0;
            string sAction = "(:action move\n";
            sAction += ":parameters (?pSource - LOCATION ?pTarget - LOCATION)\n";
            sAction += ":precondition (and (agent-at ?pSource) (adj ?pSource ?pTarget) (agent-on-ground))\n";
            sAction += ":effect (and (agent-at ?pTarget) (not (agent-at ?pSource)) (not (noise)) (not (sight))\n";
            for (int iInvader = 0; iInvader < Invaders; iInvader++)
            {
                for (iX = 1; iX <= Size; iX++)
                {
                    for (iY = 1; iY <= Size; iY++)
                    {
                        sAction += "\t(not (sight-at p" + iX + "-" + iY + "))\n";
                        sAction += "\t(when (invader-at i" + iInvader + " p" + iX + "-" + iY + ")  (oneof";

                        for (iOtherX = 1; iOtherX <= Size; iOtherX++)
                        {
                            for (iOtherY = 1; iOtherY <= Size; iOtherY++)
                            {
                                if (GetDistance(iX, iY, iOtherX, iOtherY) <= 1)
                                {
                                    if (iX != iOtherX || iY != iOtherY)
                                    {
                                        sAction += " (and (not (invader-at i" + iInvader + " p" + iX + "-" + iY + "))";
                                        sAction += " (invader-at i" + iInvader + " p" + iOtherX + "-" + iOtherY + "))";
                                    }
                                    else
                                        sAction += " (invader-at i" + iInvader + " p" + iOtherX + "-" + iOtherY + ")";
                                }
                            }
                        }
                        sAction += "))\n";
                    }
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

        private string GenerateObservationActions()
        {
            string sActions = "";
            //sActions += "(:action observe-noise\n";
            //sActions += ":observe (noise))\n";
            sActions += "(:action observe-sight\n";
            sActions += ":observe (sight))\n";
            sActions += "(:action observe-sight-at\n";
            sActions += ":parameters (?p - LOCATION)\n";
            sActions += ":observe (sight-at ?p))\n";
            /*
            sActions += "(:action observe-invader-at\n";
            sActions += ":parameters (?p - LOCATION ?i - INVADER)\n";
            sActions += ":precondition (agent-at ?p)\n";
            sActions += ":observe (invader-at ?i ?p))\n";
             */
            return sActions;
        }

        public void WriteDomain(string sPath)
        {
            if (!Directory.Exists(sPath))
                Directory.CreateDirectory(sPath);
            StreamWriter sw = new StreamWriter(sPath + @"\d.pddl");
            sw.Write(GenerateDomain());
            sw.Close();
        }

        private string GenerateDomain()
        {
            string sDomain = "(define \n";
            sDomain += "(domain " + Name + ")\n";
            sDomain += "(:types LOCATION ROCK HEIGHT)\n";
            sDomain += GenerateConstants() + "\n";
            sDomain += GeneratePredicates();
            sDomain += GenerateActions();
            sDomain += ")";
            return sDomain;
        }


        public string Name { get { return "CatchInvaders" + Size + "-" + Invaders; } }
    }
}
