using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading;

namespace PDDL
{
    class WumpusVisualizationUnit : VisualizationUnit
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
                System.Windows.Forms.Application.Run(board = new UI.frmMain("Wumpus-", GetGridSize()));
            
            
        }

        public override void Init(Domain d, Problem p)
        {
            Domain = d;
            Problem = p;
            //init the visual classes (forms,...)
            //board = new UI.frmMain();
            
            //board = new UI.frmMain();
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
            Kernel.Matrix bMatrix = new Kernel.Matrix(new Kernel.Point((byte)iSize,(byte)iSize));
            delay();
            int iX = 0, iY = 0;
            GetAgentLocation(out iX, out iY);
            cLoc = new Kernel.Point((byte)iY, (byte)iX);
            bMatrix.addCellValue(new Kernel.Point((byte)(iSize - iY), (byte)(iX - 1)), Kernel.MCellType.Agent);
            for (int i = 1; i <= iSize; i++)
                for (int j = 1; j <= iSize; j++)
                {
                    //if (IsUnNone(i, j))
                    //{
                    //    Console.WriteLine("UnNone " + i + "," + j);
                    //    // if (board.Created) board.addConsoleText("Blocked " + i + "," + j);
                    //    bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.UnNone);
                    //    bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j+1), (byte)(i - 1)), Kernel.MCellType.Pfeeling);
                    //    //bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i)), Kernel.MCellType.Pfeeling);
                    //    bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j - 1), (byte)(i - 1)), Kernel.MCellType.Pfeeling);
                    //    bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 2)), Kernel.MCellType.Pfeeling);
                    //}
                    if (IsPossibaleFeeling(i, j)&&!((i==iX)&&(j==iY)))
                    {
                        //Console.WriteLine("Breeze and Stench at " + i + "," + j);
                        // if (board.Created) board.addConsoleText("Agent might be at " + i + "," + j);
                        bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Pfeeling);
                    }
                    
                    if (IsUnSafe(i,j))
                    {
                        //Console.WriteLine("Breeze and Stench at " + i + "," + j);
                        // if (board.Created) board.addConsoleText("Agent might be at " + i + "," + j);
                        if (j > i) bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.UnNoneUp);
                        if (j < i) bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.UnNoneDown);
                    }
                    else if (IsSafe(i, j))
                    {
                        if (i == iX && j == iY)
                        {
                            //Console.WriteLine("Breeze and Stench at " + i + "," + j);
                            // if (board.Created) board.addConsoleText("Agent might be at " + i + "," + j);
                            if (j > i) bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.ANoneUp);
                            if (j < i) bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.ANoneDown);
                        }
                        else
                        {
                            //Console.WriteLine("Breeze and Stench at " + i + "," + j);
                            // if (board.Created) board.addConsoleText("Agent might be at " + i + "," + j);
                            if (j > i) bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.NoneUp);
                            if (j < i) bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.NoneDown);
                        }
                    }
                   else if ((IsFeelingBreeze(i, j))&&(IsFeelingStench(i, j)))
                    {
                        if (i == iX && j == iY)
                        {
                            //Console.WriteLine("Breeze and Stench at " + i + "," + j);
                            //if (board.Created) board.addConsoleText("Feeling Breeze & Stench at " + i + "," + j);
                            bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.AbreezeStench);
                        }
                        else
                        {
                            Console.WriteLine("Breeze and Stench at " + i + "," + j);
                            //if (board.Created) board.addConsoleText("Feeling Breeze & Stench at " + i + "," + j);
                            bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Feeling);
                        }
                    }
                    else if (IsFeelingStench(i, j))
                        {
                            if (i == iX && j == iY)
                            {
                                //Console.WriteLine("Breeze and Stench at " + i + "," + j);
                                //if (board.Created) board.addConsoleText("Feeling Stench at " + i + "," + j);
                                bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Astench);
                            }
                            else
                            {
                                Console.WriteLine("Stench at " + i + "," + j);
                                //if (board.Created) board.addConsoleText("Feeling Stench at " + i + "," + j);
                                bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Stench);
                            }
                        }
                   else if (IsFeelingBreeze(i, j))
                   {
                       if (i == iX && j == iY)
                       {
                           //Console.WriteLine("Breeze and Stench at " + i + "," + j);
                           //if (board.Created) board.addConsoleText("Feeling Breeze at " + i + "," + j);
                           bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Abreeze);
                       }
                       else
                       {
                           Console.WriteLine("Breeze at " + i + "," + j);
                           //if (board.Created) board.addConsoleText("Feeling Breeze at " + i + "," + j);
                           bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Breeze);
                        }
                    }
                    if (IsWumpus(i, j) && (IsPit(i, j)))
                    {
                        Console.WriteLine("wumpus & pit at " + i + "," + j);
                        //if (board.Created) board.addConsoleText("Wumpus & Pit at " + i + "," + j);
                        bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.WumpusPit);
                    }
                   else if (IsWumpus(i,j))
                   {
                       Console.WriteLine("wumpus at " + i + "," + j);
                       //if (board.Created) board.addConsoleText("wumpus at " + i + "," + j);
                       bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Wumpus);
                   }
                   else if (IsPit(i, j))
                   {
                       Console.WriteLine("pit at " + i + "," + j);
                       //if (board.Created) board.addConsoleText("Pit at " + i + "," + j);
                       bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Pit);
                   }
                    if (IsCrown(i, j))
                    {
                        if (i == iX && j == iY)
                        {
                            //Console.WriteLine("Breeze and Stench at " + i + "," + j);
                            // if (board.Created) board.addConsoleText("Agent might be at " + i + "," + j);
                            bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Acrown);
                        }
                        else
                        {
                            Console.WriteLine("gold at " + i + "," + j);
                            //if (board.Created) board.addConsoleText("Gold at at " + i + "," + j);
                            bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.MCellType.Crown);
                        }
                    }
                    //else bMatrix.addCellValue(new Kernel.Point((byte)(iSize - j), (byte)(i - 1)), Kernel.LCellType.None);
                }
            Console.WriteLine("Agent at " + iX + "," + iY);
            //if (board.Created) 
                board.addConsoleText(idx + ") Observation: " + obs + "\r\n    Action: " +act+"\r\n    Agent at: " + iX + "," + iY + "\r\n ----------------------------------------");
            obs = "";
            act = "";
            //if (board.Created) board.addConsoleText(idx + ") " +(GetObservation()!=""?"Observed:\r\n"+GetObservation():"No Observation\r\n") +"Action:\r\n"+ agentMove(cLoc, new Kernel.Point((byte)iY, (byte)iX)) + " (Agent at " + iX + "," + iY + ")\r\n ----------------------------------------");
            
            //if (locFlg) { if (board.Created) board.addConsoleText(idx+ ") " + agentMove(cLoc, new Kernel.Point((byte)iY, (byte)iX)) + " (Agent at " + iX + "," + iY+ ")\r\n ----------------------------------------"); }
            //else
            //{
            //    locFlg = true;
            //    if (board.Created) board.addConsoleText(idx + ") Agent at " + iX + "," + iY + "\r\n ----------------------------------------");
            //}
            idx++;
            
            //if (board.Created)
            //{
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
            return int.Parse(Problem.Name.Replace("wumpus-", ""));
        }

        public bool IsPossibaleFeeling(int iX, int iY)
        {
            if (IsUnSafe(iX, iY + 1) 
                || IsUnSafe(iX, iY - 1) 
                || IsUnSafe(iX + 1, iY) 
                || IsUnSafe(iX - 1, iY)) 
                return true;
            //if (IsUnSafe(iX, iY + 1)) return true;
            return false;
        }

        public bool IsUnSafe(int iX, int iY)
        {
            if ((iX<=0)||(iX>GetGridSize())||(iY<=0)||(iY>GetGridSize())) return false; 
            //if (iX + iY > 3)
            //    if (Math.Abs(iX - iY) == 1) return true;
            //return false;
            if (Belief.Observed == null)
                return false;
            foreach (GroundedPredicate gp in Belief.Observed)
            {
                if ((gp.Name == "safe") && (gp.Negation == false))
                {
                    string sPos = gp.Constants[0].Name;
                    sPos = sPos.Replace("p", "");
                    string[] asPos = sPos.Split('-');
                    if ((iX == int.Parse(asPos[0])) && (iY == int.Parse(asPos[1]))) return false;
                }
            }
            return true;
        }

        public bool IsSafe(int iX, int iY)
        {
            if ((iX - iY==1)&&(IsPit(iX - 1, iY + 1) || IsWumpus(iX - 1, iY + 1))) return true;
            if ((iY - iX == 1) && (IsPit(iX + 1, iY - 1) || IsWumpus(iX + 1, iY - 1))) return true;
            return false;


        }

        public bool IsFeelingBreeze(int iX, int iY)
        {
            //iX = -1;
            //iY = -1;
            if (Belief.Observed == null)
                return false;
            foreach (GroundedPredicate gp in Belief.Observed)
            {
                if ((gp.Name == "breeze")&&(gp.Negation== false))
                {
                    string sPos = gp.Constants[0].Name;
                    sPos = sPos.Replace("p", "");
                    string[] asPos = sPos.Split('-');
                    if ((iX == int.Parse(asPos[0]))&&(iY == int.Parse(asPos[1]))) return true;
                }
            }
            return false;
        }
        public bool IsFeelingStench(int iX, int iY)
        {
            //iX = -1;
            //iY = -1;
            if (Belief.Observed == null)
                return false;
            foreach (GroundedPredicate gp in Belief.Observed)
            {
                if ((gp.Name == "stench")&&(gp.Negation== false))
                {
                    string sPos = gp.Constants[0].Name;
                    sPos = sPos.Replace("p", "");
                    string[] asPos = sPos.Split('-');
                    if ((iX == int.Parse(asPos[0])) && (iY == int.Parse(asPos[1]))) return true;
                }
            }
            return false;
        }
        public bool IsWumpus(int iX, int iY)
        {
            //iX = -1;
            //iY = -1;
            if (Belief.Observed == null)
                return false;
            foreach (GroundedPredicate gp in Belief.Observed)
            {
                if ((gp.Name == "wumpus-at")&&(gp.Negation== false))
                {
                    string sPos = gp.Constants[0].Name;
                    sPos = sPos.Replace("p", "");
                    string[] asPos = sPos.Split('-');
                    if ((iX == int.Parse(asPos[0])) && (iY == int.Parse(asPos[1]))) return true;
                }
            }
            return false;
        }
        public bool IsPit(int iX, int iY)
        {
            //iX = -1;
            //iY = -1;
            if (Belief.Observed == null)
                return false;
            foreach (GroundedPredicate gp in Belief.Observed)
            {
                if ((gp.Name == "pit-at")&&(gp.Negation== false))
                {
                    string sPos = gp.Constants[0].Name;
                    sPos = sPos.Replace("p", "");
                    string[] asPos = sPos.Split('-');
                    if ((iX == int.Parse(asPos[0])) && (iY == int.Parse(asPos[1]))) return true;
                }
            }
            return false;
        }

        public bool IsCrown(int iX, int iY)
        {
            //iX = -1;
            //iY = -1;
            if (Belief.Observed == null)
                return false;
            foreach (GroundedPredicate gp in Belief.Observed)
            {
                if ((gp.Name == "gold-at") && (gp.Negation == false))
                {
                    string sPos = gp.Constants[0].Name;
                    sPos = sPos.Replace("p", "");
                    string[] asPos = sPos.Split('-');
                    if ((iX == int.Parse(asPos[0])) && (iY == int.Parse(asPos[1]))) return true;
                }
            }
            return false;
        }
        //public bool IsFeelingBreeze(int iX, int iY)
        //{
        //    GroundedPredicate gp = new GroundedPredicate("at");
        //    gp.AddConstant(new Constant("pos", "p" + iX + "-" + iY));
        //    foreach (CompoundFormula cf in Belief.Hidden)
        //        if (cf.Contains(gp))
        //            return true;
        //    return false;
        //}

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

        //public string GetObservation()
        //{
        //    string obs = "";
        //    foreach (Predicate p in Belief.Observed)
        //        if ((p.Name.Contains("feeling")) && (p.Negation == false)) obs = obs + p.Name + "\r\n";
        //    return obs;


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
