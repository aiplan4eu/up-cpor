using System;
using System.IO;

namespace CPOR
{
    class WumpusDomain
    {
        public int Size { get; private set; }
        public bool Deadends { get; private set; }
        public bool Pits { get; private set; }
        public bool GoBack { get; private set; }
        public int MoveCost { get; private set; }
        public WumpusDomain(int cSquares, int cMoveSteps, bool bDeadends, bool bGoBack)
        {
            GoBack = bGoBack;
            Deadends = bDeadends;
            Size = cSquares;
            MoveCost = cMoveSteps;
            Pits = true;
        }
        public WumpusDomain(int cSquares, bool bPits) : this(cSquares, 0, false, false)
        {
            Pits = bPits;
        }
        public void WriteProblem(string sPath)
        {
            StreamWriter sw = new StreamWriter(sPath + @"\p.pddl");
            sw.WriteLine(GenerateProblem());
            sw.Close();
        }

        private bool SafeSquare(int iX, int iY)
        {
            return Math.Abs(iX - iY) != 1 || iX + iY < 4;
        }
        /*
        private CompoundExpression GetProblem()
        {
            CompoundExpression ceProblem = new CompoundExpression();
            ceProblem.Type = "problem";
            ceProblem.SubExpressions.Add(new StringExpression("wumpus-" + Size));
            return ceProblem;
        }
        private CompoundExpression GetDomain()
        {
            CompoundExpression ceDomain = new CompoundExpression();
            ceDomain.Type = ":domain";
            ceDomain.SubExpressions.Add(new StringExpression("wumpus"));
            return ceDomain;
        }
        private Expression GenerateDomain()
        {
            CompoundExpression ceAll = new CompoundExpression();
            ceAll.Type = "define";
            ceAll.SubExpressions.Add(GetProblem());
            ceAll.SubExpressions.Add(GetDomain());
            ceAll.SubExpressions.Add(GetInitState());

            return ceAll;
        }

        private Expression GetAt(int iX, int iY)
        {
            CompoundExpression ceAt = new CompoundExpression();
            ceAt.Type = "at";
            ceAt.SubExpressions.Add(new StringExpression("p" + iX + "-" + iY));
            return ceAt;
        }
        private Expression GetAdjacent(int iX1, int iY1, int iX2, int iY2)
        {
            CompoundExpression ceAdj = new CompoundExpression();
            ceAdj.Type = "adj";
            ceAdj.SubExpressions.Add(new StringExpression("p" + iX1 + "-" + iY1));
            ceAdj.SubExpressions.Add(new StringExpression("p" + iX2 + "-" + iY2));
            return ceAdj;
        }
        private Expression GetInitState()
        {
            CompoundExpression ceInit = new CompoundExpression();
            ceInit.Type = ":init";
            CompoundExpression ceAnd = new CompoundExpression();
            ceAnd.Type = "and";
            ceInit.SubExpressions.Add(ceAnd);
            ceAnd.SubExpressions.Add(GetAt(1, 1));
            ceAnd.SubExpressions.Add(new StringExpression("alive"));


            return ceInit;
        }
        */

        private string GenerateProblem()
        {
            string sDomain = "(define \n";
            sDomain += "(problem Wumpus-" + Size + ")\n";
            sDomain += "(:domain Wumpus-" + Size + ")\n";
            sDomain += "(:goal (and (got-the-treasure) (alive)))\n";
            sDomain += GetInitState();
            sDomain += ")";
            return sDomain;
        }

        private string GetPosition(int iX, int iY)
        {
            return "p" + iX + "-" + iY;
        }
        private string GetAdjacent(int iX1, int iY1, int iX2, int iY2)
        {
            return "(adj " + GetPosition(iX1, iY1) + " " + GetPosition(iX2, iY2) + ")\n";
        }
        private string GetAdjacents()
        {
            string sAdjacents = "";
            for (int iX = 1; iX <= Size; iX++)
            {
                for (int iY = 1; iY <= Size; iY++)
                {
                    if (iX > 1)
                        sAdjacents += GetAdjacent(iX, iY, iX - 1, iY);
                    if (iX < Size)
                        sAdjacents += GetAdjacent(iX, iY, iX + 1, iY);
                    if (iY > 1)
                        sAdjacents += GetAdjacent(iX, iY, iX, iY - 1);
                    if (iY < Size)
                        sAdjacents += GetAdjacent(iX, iY, iX, iY + 1);
                }
            }
            return sAdjacents;
        }
        private string GetSafes()
        {
            string sSafes = "";
            for (int iX = 1; iX <= Size; iX++)
            {
                for (int iY = 1; iY <= Size; iY++)
                {
                    if (Math.Abs(iX - iY) != 1 || iX + iY < 5)
                        sSafes += "(safe " + GetPosition(iX, iY) + ")\n";
                }
            }
            return sSafes;
        }
        private string GetUnsafes()
        {
            string sUnsafes = "";
            for (int i = 2; i < Size; i++)
            {
                sUnsafes += "(oneof (safe " + GetPosition(i + 1, i) + ") (safe " + GetPosition(i, i + 1) + "))\n";
            }
            return sUnsafes;
        }
        private string GetWumpusPitLocations()
        {
            string sUnsafes = "";
            for (int i = 2; i < Size; i++)
            {
                string sPosition = GetPosition(i + 1, i);
                if (Pits)
                    sUnsafes += "(oneof (safe " + sPosition + ") (or (wumpus-at " + sPosition + ") (pit-at " + sPosition + ")))\n";
                else
                    sUnsafes += "(oneof (safe " + sPosition + ") (wumpus-at " + sPosition + "))\n";

                sPosition = GetPosition(i, i + 1);
                if (Pits)
                    sUnsafes += "(oneof (safe " + sPosition + ") (or (wumpus-at " + sPosition + ") (pit-at " + sPosition + ")))\n";
                else
                    sUnsafes += "(oneof (safe " + sPosition + ") (wumpus-at " + sPosition + "))\n";
            }
            return sUnsafes;
        }
        private string GetStench(int iX, int iY)
        {
            int cStenchLocations = 0;
            string sStench = "(oneof (not (stench " + GetPosition(iX, iY) + "))";
            string sLocations = "";
            if (iX > 1 && !SafeSquare(iX - 1, iY))
            {
                sLocations += " (wumpus-at " + GetPosition(iX - 1, iY) + ")";
                cStenchLocations++;
            }
            if (iX < Size && !SafeSquare(iX + 1, iY))
            {
                sLocations += " (wumpus-at " + GetPosition(iX + 1, iY) + ")";
                cStenchLocations++;
            }
            if (iY > 1 && !SafeSquare(iX, iY - 1))
            {
                sLocations += " (wumpus-at " + GetPosition(iX, iY - 1) + ")";
                cStenchLocations++;
            }
            if (iY < Size && !SafeSquare(iX, iY + 1))
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
        private string GetBreeze(int iX, int iY)
        {
            int cPitLocations = 0;
            string sBreeze = "(oneof (not (breeze " + GetPosition(iX, iY) + "))";
            string sLocations = "";
            if (iX > 1 && !SafeSquare(iX - 1, iY))
            {
                sLocations += " (pit-at " + GetPosition(iX - 1, iY) + ")";
                cPitLocations++;
            }
            if (iX < Size && !SafeSquare(iX + 1, iY))
            {
                sLocations += " (pit-at " + GetPosition(iX + 1, iY) + ")";
                cPitLocations++;
            }
            if (iY > 1 && !SafeSquare(iX, iY - 1))
            {
                sLocations += " (pit-at " + GetPosition(iX, iY - 1) + ")";
                cPitLocations++;
            }
            if (iY < Size && !SafeSquare(iX, iY + 1))
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
            sInit += "(at p1-1)" + "\n";
            sInit += "(gold-at p" + Size + "-" + Size + ")" + "\n";
            sInit += "(alive)" + "\n";
            if (MoveCost > 0)
                sInit += "(MoveStep ms0)\n";
            sInit += GetAdjacents() + "\n";
            sInit += GetSafes() + "\n";
            sInit += GetUnsafes() + "\n";
            sInit += GetWumpusPitLocations() + "\n";
            sInit += GetStenchs() + "\n";
            if (Pits)
                sInit += GetBreezes() + "\n";
            sInit += ")\n)\n";
            return sInit;
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
            if (MoveCost > 0)
                sw.Write("(:types POS MOVE_STEP)\n");
            else
                sw.Write("(:types POS)\n");
            sw.Write(GenerateConstants() + "\n");
            sw.Write(GeneratePredicates());
            GenerateActions(sw);
            sw.Write(")");
        }

        private void GenerateActions(StreamWriter sw)
        {
            if (MoveCost > 0)
                sw.WriteLine(GeneratePrepareMoveActions());
            if (Deadends)
                sw.WriteLine(GenerateMoveActionWithDeadends());
            else if (GoBack)
                sw.WriteLine(GenerateMoveActionWithGoBack());
            else
                sw.WriteLine(GenerateMoveAction());
            sw.WriteLine(GenerateSmellAction());
            if (Pits)
                sw.WriteLine(GenerateFeelBreezeAction());
            if (GoBack)
                sw.WriteLine(GenerateObserveLocationAction());
            sw.WriteLine(GenerateGrabAction());
        }

        private string GenerateMoveAction()
        {
            string sAction = "(:action move\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            if (MoveCost > 0)
            {
                sAction += "\t:precondition (and (MoveStep ms" + (MoveCost - 1) + ") (adj ?i ?j) (at ?i) (alive) (safe ?j))\n";
                sAction += "\t:effect (and (not (MoveStep ms" + (MoveCost - 1) + ")) (MoveStep ms0) (not (at ?i)) (at ?j))\n";
            }
            else
            {
                sAction += "\t:precondition (and (adj ?i ?j) (at ?i) (alive) (safe ?j))\n";
                sAction += "\t:effect (and (not (at ?i)) (at ?j))\n";
            }
            sAction += ")\n";
            return sAction;
        }
        private string GeneratePrepareMoveActions()
        {
            string sActions = "";
            string sAction = "";
            for (int iMoveStep = 0; iMoveStep < MoveCost - 1; iMoveStep++)
            {
                sAction = "(:action prepare-move" + iMoveStep + "\n";
                sAction += "\t:precondition (and (MoveStep ms" + iMoveStep + ") (alive))\n";
                sAction += "\t:effect (and (not (MoveStep ms" + iMoveStep + ")) (MoveStep ms" + (iMoveStep + 1) + "))\n";
                sAction += ")\n";
                sActions += sAction;
            }
            return sActions;
        }
        private string GenerateMoveActionWithDeadends()
        {
            string sAction = "(:action move\n";

            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            if (MoveCost > 0)
            {
                sAction += "\t:precondition (and (MoveStep ms" + (MoveCost - 1) + ") (adj ?i ?j) (at ?i) (alive))\n";
                sAction += "\t:effect (and (MoveStep ms0) (not (MoveStep ms" + (MoveCost - 1) + "))\n";
            }
            else
            {
                sAction += "\t:precondition (and (adj ?i ?j) (at ?i) (alive))\n";
                sAction += "\t:effect (and \n";
            }
            sAction += "\t\t(when (safe ?j) (and (not (at ?i)) (at ?j)))\n";
            sAction += "\t\t(when (not (safe ?j)) (not (alive)))\n";
            sAction += "\t)\n";
            //sAction += "\t:observe (safe ?j)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateMoveActionWithGoBack()
        {
            string sAction = "(:action move\n";
            sAction += "\t:parameters (?i - pos ?j - pos)\n";
            if (MoveCost > 0)
            {
                sAction += "\t:precondition (and (MoveStep ms" + (MoveCost - 1) + ") (adj ?i ?j) (at ?i) (alive))\n";
                sAction += "\t:effect (and (MoveStep ms0) (not (MoveStep ms" + (MoveCost - 1) + "))\n";
            }
            else
            {
                sAction += "\t:precondition (and (adj ?i ?j) (at ?i) (alive))\n";
                sAction += "\t:effect (and \n";
            }
            sAction += "\t\t(when (safe ?j) (and (not (at ?i)) (at ?j)))\n";
            sAction += "\t\t(when (not (safe ?j)) (and (not (at ?i)) (at p1-1)))\n";
            sAction += "\t)\n";
            //sAction += "\t:observe (safe ?j)\n";
            sAction += ")\n";
            return sAction;
        }

        private string GenerateSmellAction()
        {
            string sAction = "(:action smell-wumpus\n";
            sAction += "\t:parameters (?i - pos)\n";
            sAction += "\t:precondition (and (alive) (at ?i))\n";
            sAction += "\t:observe (stench ?i)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateGrabAction()
        {
            string sAction = "(:action grab\n";
            sAction += "\t:parameters (?i - pos)\n";
            sAction += "\t:precondition (and (alive) (gold-at ?i) (at ?i))\n";
            sAction += "\t:effect (and (got-the-treasure) (not (gold-at ?i)))\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateFeelBreezeAction()
        {
            string sAction = "(:action feel-breeze\n";
            sAction += "\t:parameters (?i - pos)\n";
            sAction += "\t:precondition (and (alive) (at ?i))\n";
            sAction += "\t:observe (breeze ?i)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateObserveLocationAction()
        {
            string sAction = "(:action observe-location\n";
            sAction += "\t:parameters (?i - pos)\n";
            sAction += "\t:precondition (and (alive))\n";
            sAction += "\t:observe (at ?i)\n";
            sAction += ")\n";
            return sAction;
        }
        private string GenerateConstants()
        {
            string sConstants = "(:constants";
            for (int i = 1; i <= Size; i++)
                for (int j = 1; j <= Size; j++)
                    sConstants += " p" + i + "-" + j;
            sConstants += " - pos";
            if (MoveCost > 0)
            {
                for (int i = 0; i < MoveCost; i++)
                    sConstants += " ms" + i;
                sConstants += " - MOVE_STEP";
            }
            sConstants += ")\n";
            return sConstants;
        }

        private string GeneratePredicates()
        {
            string sPredictes = "(:predicates\n";
            sPredictes += "\t(adj ?i ?j - pos)\n";
            sPredictes += "\t(at ?i - pos)\n";
            sPredictes += "\t(safe ?i - pos)\n";
            sPredictes += "\t(wumpus-at ?i - pos)\n";
            sPredictes += "\t(stench ?i - pos)\n";
            sPredictes += "\t(gold-at ?i - pos)\n";
            if (Pits)
            {
                sPredictes += "\t(breeze ?i - pos)\n";
                sPredictes += "\t(pit-at ?i - pos)\n";
            }
            sPredictes += "\t(got-the-treasure)\n";
            if (MoveCost > 0)
                sPredictes += "\t(MoveStep ?ms - MOVE_STEP)\n";
            sPredictes += "\t(alive)\n";
            sPredictes += ")\n";
            return sPredictes;
        }

        public string Name { get { return "Wumpus-" + Size; } }
    }
}
