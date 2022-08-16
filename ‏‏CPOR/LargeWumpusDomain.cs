using System.Collections.Generic;
using System.IO;
using System.Linq;

namespace CPOR
{
    class LargeWumpusDomain
    {
        public static int WumpusCount { get; set; }
        public static int PitCount { get; set; }
        public static int Size { get; private set; }
        public LargeWumpusDomain(int cSquares)
        {
            Size = cSquares;
        }
        public void WriteProblem(string sPath)
        {
            StreamWriter sw = new StreamWriter(sPath + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }


        private string GenerateProblem()
        {
            string sDomain = "(define \n";
            sDomain += "(problem LargeWumpus-" + Size + ")\n";
            sDomain += "(:domain LargeWumpus-" + Size + ")\n";
            sDomain += "(:goal (and (got-the-treasure) (alive)))\n";
            sDomain += GetInitState();
            sDomain += ")";
            return sDomain;
        }

        private string GetPosition(int iX, int iY)
        {
            //return "p" + iX + "-" + iY;
            return "p-" + iX + " p-" + +iY;
        }

        private string GetStenchII(int iX, int iY)
        {
            int cStenchLocations = 0;
            string sStench = "(oneof (not (stench " + GetPosition(iX, iY) + "))";
            string sLocations = "";
            if (iX > 1)
            {
                sLocations += " (wumpus-at " + GetPosition(iX - 1, iY) + ")";
                cStenchLocations++;
            }
            if (iX < Size)
            {
                sLocations += " (wumpus-at " + GetPosition(iX + 1, iY) + ")";
                cStenchLocations++;
            }
            if (iY > 1)
            {
                sLocations += " (wumpus-at " + GetPosition(iX, iY - 1) + ")";
                cStenchLocations++;
            }
            if (iY < Size)
            {
                sLocations += " (wumpus-at " + GetPosition(iX, iY + 1) + ")";
                cStenchLocations++;
            }
            if (cStenchLocations == 0)
                return "";
            if (cStenchLocations == 1)
                sStench += sLocations;
            else
                sStench += " (or" + sLocations + ")";

            sStench += ")\n";
            return sStench;
        }

        private string GetStench(int iX, int iY)
        {
            int cStenchLocations = 0;
            string sStench = "(or (not (wumpus-at " + GetPosition(iX, iY) + "))";
            string sLocations = "";
            if (iX > 1)
            {
                sLocations += " (stench " + GetPosition(iX - 1, iY) + ")";
                cStenchLocations++;
            }
            if (iX < Size)
            {
                sLocations += " (stench " + GetPosition(iX + 1, iY) + ")";
                cStenchLocations++;
            }
            if (iY > 1)
            {
                sLocations += " (stench " + GetPosition(iX, iY - 1) + ")";
                cStenchLocations++;
            }
            if (iY < Size)
            {
                sLocations += " (stench " + GetPosition(iX, iY + 1) + ")";
                cStenchLocations++;
            }
            if (cStenchLocations == 0)
                return "";
            if (cStenchLocations == 1)
                sStench += sLocations;
            else
                sStench += " (and" + sLocations + ")";

            sStench += ")\n";
            return sStench;
        }
        private string GetStenchs()
        {
            string sStenches = "";
            for (int iX = 1; iX <= Size; iX++)
            {
                for (int iY = 1; iY <= Size; iY++)
                {
                    sStenches += GetStench(iX, iY);
                }
            }
            return sStenches;
        }
        private string GetBreezeII(int iX, int iY)
        {
            int cPitLocations = 0;
            string sBreeze = "(oneof (not (breeze " + GetPosition(iX, iY) + "))";
            string sLocations = "";
            if (iX > 1)
            {
                sLocations += " (pit-at " + GetPosition(iX - 1, iY) + ")";
                cPitLocations++;
            }
            if (iX < Size)
            {
                sLocations += " (pit-at " + GetPosition(iX + 1, iY) + ")";
                cPitLocations++;
            }
            if (iY > 1)
            {
                sLocations += " (pit-at " + GetPosition(iX, iY - 1) + ")";
                cPitLocations++;
            }
            if (iY < Size)
            {
                sLocations += " (pit-at " + GetPosition(iX, iY + 1) + ")";
                cPitLocations++;
            }
            if (cPitLocations == 0)
                return "";
            if (cPitLocations == 1)
                sBreeze += sLocations;
            else
                sBreeze += " (or" + sLocations + ")";

            sBreeze += ")\n";
            return sBreeze;
        }

        private string GetBreeze(int iX, int iY)
        {
            int cPitLocations = 0;
            string sBreeze = "(or (not (pit-at " + GetPosition(iX, iY) + "))";
            string sLocations = "";
            if (iX > 1)
            {
                sLocations += " (breeze " + GetPosition(iX - 1, iY) + ")";
                cPitLocations++;
            }
            if (iX < Size)
            {
                sLocations += " (breeze " + GetPosition(iX + 1, iY) + ")";
                cPitLocations++;
            }
            if (iY > 1)
            {
                sLocations += " (breeze " + GetPosition(iX, iY - 1) + ")";
                cPitLocations++;
            }
            if (iY < Size)
            {
                sLocations += " (breeze " + GetPosition(iX, iY + 1) + ")";
                cPitLocations++;
            }
            if (cPitLocations == 0)
                return "";
            if (cPitLocations == 1)
                sBreeze += sLocations;
            else
                sBreeze += " (and" + sLocations + ")";

            sBreeze += ")\n";
            return sBreeze;
        }
        private string GetBreezes()
        {
            string sBreezes = "";
            for (int iX = 1; iX <= Size; iX++)
            {
                for (int iY = 1; iY <= Size; iY++)
                {
                    sBreezes += GetBreeze(iX, iY);
                }
            }
            return sBreezes;
        }

        private string GetInitState()
        {
            string sInit = "(:init\n";
            sInit += "(and\n";
            sInit += "(at-x p-1) (at-y p-1)" + "\n";
            sInit += "(alive)" + "\n";
            sInit += GetGold() + "\n";
            sInit += GetSafes() + "\n";
            sInit += GetStenchs() + "\n";
            sInit += GetBreezes() + "\n";
            sInit += ")\n)\n";
            return sInit;
        }

        private string GetSafes()
        {
            string sSafe = "";
            for (int x = 1; x <= Size; x++)
            {
                for (int y = 1; y <= Size; y++)
                {
                    sSafe += "(oneof (safe " + GetPosition(x, y) + ") (wumpus-at " + GetPosition(x, y) + ") (pit-at " + GetPosition(x, y) + "))\n";
                }
            }
            return sSafe;
        }

        private string GetGold()
        {
            string sGold = "(oneof";
            for (int x = 1; x <= Size; x++)
            {
                for (int y = 1; y <= Size; y++)
                {
                    sGold += " (gold-at " + GetPosition(x, y) + ")";
                }
            }
            sGold += ")\n";
            return sGold;
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

        private void GenerateDomain(StreamWriter sw)
        {
            sw.Write("(define \n");
            sw.Write("(domain " + Name + ")\n");
            sw.Write("(:types POS)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }

        private void GenerateActions(StreamWriter sw)
        {
            sw.WriteLine(GenerateMoveActions());
            sw.WriteLine(GenerateSmellAction());
            sw.WriteLine(GenerateFeelBreezeAction());
            sw.WriteLine(GenerateObserveGoldAction());
            sw.WriteLine(GenerateGrabAction());
        }

        private string GenerateObserveGoldAction()
        {
            string sAction = "(:action observe-gold\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (alive) (at-x ?x) (at-y ?y))\n";
            sAction += "\t:observe (gold-at ?x ?y)\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateMoveActions()
        {
            string sMoveActions = "";
            sMoveActions += GenerateCheckAliveAction();
            sMoveActions += GenerateMoveUpAction();
            sMoveActions += GenerateMoveDownAction();
            sMoveActions += GenerateMoveLeftAction();
            sMoveActions += GenerateMoveRightAction();
            return sMoveActions;
        }
        private string GenerateCheckAliveAction()
        {
            string sAction = "(:action check-alive\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (at-x ?x) (at-y ?y))\n";
            sAction += "\t:effect (when (not (safe ?x ?y)) (not (alive)))\n";
            sAction += "\t:observe (alive)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateMoveUpAction()
        {
            string sAction = "(:action move-up\n";
            sAction += "\t:precondition (alive)\n";
            sAction += "\t:effect (and \n";
            for (int y = 2; y <= Size; y++)
                sAction += "\t\t(when (at-y p-" + y + ") (and (not (at-y p-" + y + ")) (at-y p-" + (y - 1) + ")))\n";
            sAction += "))\n";
            return sAction;
        }
        private string GenerateMoveDownAction()
        {
            string sAction = "(:action move-down\n";
            sAction += "\t:precondition (alive)\n";
            sAction += "\t:effect (and \n";
            for (int y = 1; y <= Size - 1; y++)
                sAction += "\t\t(when (at-y p-" + y + ") (and (not (at-y p-" + y + ")) (at-y p-" + (y + 1) + ")))\n";
            sAction += "))\n";
            return sAction;
        }
        private string GenerateMoveLeftAction()
        {
            string sAction = "(:action move-left\n";
            sAction += "\t:precondition (alive)\n";
            sAction += "\t:effect (and \n";
            for (int x = 2; x <= Size; x++)
                sAction += "\t\t(when (at-x p-" + x + ") (and (not (at-x p-" + x + ")) (at-x p-" + (x - 1) + ")))\n";
            sAction += "))\n";
            return sAction;
        }
        private string GenerateMoveRightAction()
        {
            string sAction = "(:action move-right\n";
            sAction += "\t:precondition (alive)\n";
            sAction += "\t:effect (and \n";
            for (int x = 1; x <= Size - 1; x++)
                sAction += "\t\t(when (at-x p-" + x + ") (and (not (at-x p-" + x + ")) (at-x p-" + (x + 1) + ")))\n";
            sAction += "))\n";
            return sAction;
        }

        private string GenerateSmellAction()
        {
            string sAction = "(:action smell-wumpus\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (alive) (at-x ?x) (at-y ?y))\n";
            sAction += "\t:observe (stench ?x ?y)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateGrabAction()
        {
            string sAction = "(:action grab\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (alive) (gold-at ?x ?y)  (at-x ?x) (at-y ?y))\n";
            sAction += "\t:effect (and (got-the-treasure) (not (gold-at ?x ?y)))\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateFeelBreezeAction()
        {
            string sAction = "(:action feel-breeze\n";
            sAction += "\t:parameters (?x - pos ?y - pos)\n";
            sAction += "\t:precondition (and (alive) (at-x ?x) (at-y ?y))\n";
            sAction += "\t:observe (breeze ?x ?y)\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateConstants()
        {
            string sConstants = "(:constants";
            for (int i = 1; i <= Size; i++)
                sConstants += " p-" + i;
            sConstants += " - pos";

            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredictes = "(:predicates\n";
            sPredictes += "\t(at-x ?i - pos)\n";
            sPredictes += "\t(at-y ?i - pos)\n";
            sPredictes += "\t(safe ?x - pos ?y - pos)\n";
            sPredictes += "\t(wumpus-at ?x - pos ?y - pos)\n";
            sPredictes += "\t(stench ?x - pos ?y - pos)\n";
            sPredictes += "\t(gold-at ?x - pos ?y - pos)\n";
            sPredictes += "\t(breeze ?x - pos ?y - pos)\n";
            sPredictes += "\t(pit-at ?x - pos ?y - pos)\n";
            sPredictes += "\t(got-the-treasure)\n";
            sPredictes += "\t(alive)\n";
            sPredictes += ")\n";
            return sPredictes;
        }

        public string Name { get { return "LargeWumpus-" + Size; } }



        static HashSet<int> VisitedLocations = new HashSet<int>();

        private static GroundedPredicate GetSafe(int iX, int iY)
        {
            GroundedPredicate gpSafe = new GroundedPredicate("safe");
            gpSafe.AddConstant(new Constant("pos", "p-" + iX));
            gpSafe.AddConstant(new Constant("pos", "p-" + iY));
            return gpSafe;

        }

        public static List<string> LargeWumpusHeuristic(PartiallySpecifiedState pssCurrent, Domain d)
        {
            List<string> lActions = new List<string>();
            GroundedPredicate gpAtX = null, gpAtY = null;
            foreach (GroundedPredicate gp in pssCurrent.Observed)
            {
                if (!gp.Negation)
                {
                    if (gp.Name == "at-x")
                        gpAtX = gp;
                    if (gp.Name == "at-y")
                        gpAtY = gp;
                }
            }
            string sX = gpAtX.Constants[0].Name;
            string sY = gpAtY.Constants[0].Name;
            int iX = int.Parse(sX.Split('-')[1]);
            int iY = int.Parse(sY.Split('-')[1]);
            VisitedLocations.Add(iX * 1000 + iY);

            GroundedPredicate gpAlive = new GroundedPredicate("alive");
            if (pssCurrent.Hidden.Contains(gpAlive))
                lActions.Add("check-alive_" + sX + "_" + sY);
            GroundedPredicate gpStench = new GroundedPredicate("stench");
            gpStench.AddConstant(gpAtX.Constants[0]);
            gpStench.AddConstant(gpAtY.Constants[0]);
            if (pssCurrent.Hidden.Contains(gpStench))
                lActions.Add("smell-wumpus " + sX + " " + sY);
            GroundedPredicate gpBreeze = new GroundedPredicate("breeze");
            gpBreeze.AddConstant(gpAtX.Constants[0]);
            gpBreeze.AddConstant(gpAtY.Constants[0]);
            if (pssCurrent.Hidden.Contains(gpBreeze))
                lActions.Add("feel-breeze " + sX + " " + sY);
            GroundedPredicate gpGold = new GroundedPredicate("gold-at");
            gpGold.AddConstant(gpAtX.Constants[0]);
            gpGold.AddConstant(gpAtY.Constants[0]);
            if (pssCurrent.Hidden.Contains(gpGold))
                lActions.Add("observe-gold " + sX + " " + sY);

            if (lActions.Count == 0)
            {
                List<string> lNotVisited = new List<string>();
                List<string> lSafe = new List<string>();
                if (iX > 1)
                {
                    if (!VisitedLocations.Contains((iX - 1) * 1000 + iY))
                        lNotVisited.Add("move-left");
                    if (pssCurrent.Observed.Contains(GetSafe(iX - 1, iY)))
                        lSafe.Add("move-left");
                }
                if (iX < Size)
                {
                    if (!VisitedLocations.Contains((iX + 1) * 1000 + iY))
                        lNotVisited.Add("move-right");
                    if (pssCurrent.Observed.Contains(GetSafe(iX + 1, iY)))
                        lSafe.Add("move-right");
                }
                if (iY > 1)
                {
                    if (!VisitedLocations.Contains(iX * 1000 + (iY - 1)))
                        lNotVisited.Add("move-up");
                    if (pssCurrent.Observed.Contains(GetSafe(iX, iY - 1)))
                        lSafe.Add("move-up");
                }
                if (iY < Size)
                {
                    if (!VisitedLocations.Contains(iX * 1000 + (iY + 1)))
                        lNotVisited.Add("move-down");
                    if (pssCurrent.Observed.Contains(GetSafe(iX, iY + 1)))
                        lSafe.Add("move-down");
                }
                List<string> lSafeAndNotVisited = new List<string>(lSafe.Intersect(lNotVisited));
                if (lSafeAndNotVisited.Count > 0)
                {
                    int idx = RandomGenerator.Next(lSafeAndNotVisited.Count);
                    lActions.Add(lSafeAndNotVisited[idx]);
                }
                else if (lSafe.Count > 0)
                {
                    int idx = RandomGenerator.Next(lSafe.Count);
                    lActions.Add(lSafe[idx]);
                }
                else
                {
                    int idx = RandomGenerator.Next(4);
                    if (idx == 0)
                        lActions.Add("move-down");
                    if (idx == 1)
                        lActions.Add("move-up");
                    if (idx == 2)
                        lActions.Add("move-left");
                    if (idx == 3)
                        lActions.Add("move-right");
                }
            }


            return lActions;
        }


    }
}
