using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;

namespace PDDL
{
    class LocalizationVisualizationUnit : VisualizationUnit
    {
        private Domain Domain;
        private Problem Problem;
        private BeliefState Belief;
        private UI.frmMain board;
        Thread t;
        private bool locFlg;
        private Kernel.Point cLoc;
        private int idx=1;
        string obs="";
        string act = "";

        public void startingGUI()
        {
                System.Windows.Forms.Application.EnableVisualStyles();
                System.Windows.Forms.Application.Run(board = new UI.frmMain("sliding-doors-", GetGridSize()));        
        }

        public override void Init(Domain d, Problem p)
        {
            Domain = d;
            Problem = p;
            //init the visual classes (forms,...)
            t = new Thread(new ThreadStart(this.startingGUI));
            t.Start();
            locFlg = false;
        }

        public void delay()
        {
            int flg = 99;
            while (flg >= board.delay)
            {
                Thread.Sleep(10);
                if (flg>0) flg--;
            }
        }

        //public string agentMove(Kernel.Point pLoc, Kernel.Point cLoc)
        //{

        //    switch (cLoc.Column - pLoc.Column)
        //    {
        //        case 1:
        //            return "Agent Moves Right";

        //        case -1:
        //            return "Agent Moves Loft";

        //    }
        //    switch (cLoc.Row - pLoc.Row)
        //    {
        //        case 1:
        //            return "Agent Moves Up";

        //        case -1:
        //            return "Agent Moves Down";

        //    }
        //    return "Agent Didnt Move";
        //}

        public override void UpdateState(BeliefState bs)
        {
            Belief = bs;
            int iSize = GetGridSize();
            //your code here
            Kernel.Matrix bMatrix = new Kernel.Matrix(new Kernel.Point((byte)iSize, (byte)iSize));
            delay();
            int iX = 0, iY = 0;
            GetAgentLocation(out iX, out iY);
            for (int i = 1; i <= iSize; i++)
                for (int j = 1; j <= iSize; j++)
                {
                    if (IsLocationBlocked(i, j))
                    {
                        Console.WriteLine("Blocked " + i + "," + j);
                        // if (board.Created) board.addConsoleText("Blocked " + i + "," + j);
                        bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)),  Kernel.LCellType.Fix);
                    }
                    else if (IsPossibleLocation(i, j))
                    {
                        Console.WriteLine("Agent might be at " + i + "," + j);
                        // if (board.Created) board.addConsoleText("Agent might be at " + i + "," + j);
                        bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.LCellType.PAgent);
                    }
                    else bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.LCellType.None);
                }
            Console.WriteLine("Agent at " + iX + "," + iY);
           // if (board.Created) 
                board.addConsoleText(idx + ") Observation: " + obs + "\r\n    Action: " + act + "\r\n    Agent at: " + iX + "," + iY + "\r\n ----------------------------------------");
            obs = "";
            act = "";
            //if (board.Created) board.addConsoleText(idx + ") " + "Observed:" + GetObservation(bs) + "\r\n Action:" + agentMove(cLoc, new Kernel.Point((byte)iY, (byte)iX)) + "\r\n(Agent at " + iX + "," + iY + ")\r\n ----------------------------------------");

            //if (locFlg) { if (board.Created) board.addConsoleText(idx+ ") " + agentMove(cLoc, new Kernel.Point((byte)iY, (byte)iX)) + " (Agent at " + iX + "," + iY+ ")\r\n ----------------------------------------"); }
            //else
            //{
            //    locFlg = true;
            //    if (board.Created) board.addConsoleText(idx + ") Agent at " + iX + "," + iY + "\r\n ----------------------------------------");
            //}
            idx++;
            cLoc = new Kernel.Point((byte)iY, (byte)iX);
            bMatrix.addCellValue(new Kernel.Point((byte)(iSize - iY), (byte)(iX - 1)), Kernel.LCellType.Agent);
            //if (board.Created)
           // {
                board.setMatrix(bMatrix);
                if (board.fF == true)
                {
                    board.fF = false;
                    board.stopSpeed();
                }
           // }
     

        }

        


        public override void Dispose()
        {

            System.Windows.Forms.Application.Exit();
        }

        public int GetGridSize()
        {
            return int.Parse(Problem.Name.Replace("sliding-doors-", ""));
        }


        public bool IsLocationBlocked(int iX, int iY)
        {
            GroundedPredicate gp = new GroundedPredicate("at");
            gp.AddConstant(new Constant("pos", "p" + iX + "-" + iY));
            Action aChecking = Domain.GetAction("checking");
            if (aChecking.Effects.Contains(gp))
                return false;
            return true;
        }

        public bool IsPossibleLocation(int iX, int iY)
        {
            GroundedPredicate gp = new GroundedPredicate("at");
            gp.AddConstant(new Constant("pos", "p" + iX + "-" + iY));
            foreach (CompoundFormula cf in Belief.Hidden)
                if (cf.Contains(gp))
                    return true;
            return false;
        }

        public void GetAgentLocation(out int iX, out int iY)
        {
            iX = -1;
            iY = -1;
            if (Belief.UnderlyingEnvironmentState == null)
                return;
            foreach (GroundedPredicate gp in Belief.UnderlyingEnvironmentState.Predicates)
            {
                if (gp.Name == "at")
                {
                    string sPos = gp.Constants[0].Name;
                    sPos = sPos.Replace("p", "");
                    string[] asPos = sPos.Split('-');
                    iX = int.Parse(asPos[0]);
                    iY = int.Parse(asPos[1]);
                    return;
                }
            }
        }

        //public string GetObservation(BeliefState bs)
        //{
        //    string obs = "";
        //    foreach (Predicate p in bs.Observed)
        //        if ((p.Name.Contains("free")) && (p.Negation == false)) obs = obs + p.Name + "\r\n";
        //    return obs;
        //    //

        //}

        public override void addObservation(Formula s)
        {
            obs = obs + s;
        }

        public override void addAction(string s)
        {
            act = act + s;
        }

    }
}
