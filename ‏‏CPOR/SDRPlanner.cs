using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;

namespace CPOR
{
    public enum DeadEndExistence { DeadEndFalse = 0, DeadEndTrue = 1, MaybeDeadEnd = 2 };
    public enum DeadendStrategy { Active, Lazy, Both, Classical };

    public class SDRPlanner
    {
        //test
        public static bool SDR_OBS { set; get; }

        public enum Translations { SDR, MPSRTagPartitions, MPSRTags, BestCase, Conformant, SingleStateK }
        public enum Planners { FF, FFsa, FFha, MIPS, MetricFF, LPG, FD, CPT, FFX, FF_WSL, TRAPPER_WSL, LocalFSP }
        public static Planners Planner = Planners.LocalFSP;
        public static bool UseFilesForPlanners = true;

        public static bool AllowChoosingNonDeterministicOptions = true;
        private static Dictionary<Thread, Process> FFProcesses = new Dictionary<Thread, Process>();

        public static bool TryImmediatePlan = false;
        public static Translations Translation = Translations.SDR;
        //public static Translations Translation = Translations.SingleStateK;

        public ExecutionData Data { get; private set; }
        // OptimizeMemoryConsumption= true in offline planning 
        //OptimizeMemoryConsumption= false in online planning 
        public static bool OptimizeMemoryConsumption = false;
        // for offline planning use thi flag with true
        public static bool ComputeCompletePlanTree = false;
        //  use this flag with false


        //public static bool ComputeCompletePlanTree = false;
        public static TimeSpan PlannerTimeout = new TimeSpan(0, 1, 0);
        public static bool WriteAllKVariations = false;
        public static bool ConsiderStateNegations = false;
        public static bool SplitConditionalEffects = false;
        public static bool RemoveAllKnowledge = true;
        public static bool ForceTagObservations = false;
        public static bool EnforceCNF = false;
        public static bool UseDomainSpecificHeuristics = false;

        public static bool AddAllKnownToGiven { get; set; }
        public static bool AddTagRefutationToGoal { get; set; }

        public static List<string> SimulationStartState { get; set; }
        public static string GivenPlanFile = null;

        public static int TagsCount { get; set; }
        public bool maybeDead = false;
        public bool closeDead = false;
        public bool randomState = false;


        public static DeadendStrategy DeadendStrategy = DeadendStrategy.Lazy;


        //TODO - to remove
        public int amount_of_offline_pruned_states;

        public SDRPlanner(string sPath, string DeadEndFile, Domain d, Problem p, bool bOnline, DeadendStrategy ds)
        {
            ComputeCompletePlanTree = !bOnline;
            DeadendStrategy = ds;
            Data = new ExecutionData(sPath, DeadEndFile, d, p, ds);
        }

        public SDRPlanner(string sPath, Domain d, Problem p, bool bOnline)
        {
            ComputeCompletePlanTree = !bOnline;
            DeadendStrategy = DeadendStrategy.Lazy;
            Data = new ExecutionData(sPath, "", d, p, DeadendStrategy);
        }
        List<string> Plan(string sPath, string deadEndFile, PartiallySpecifiedState pssCurrent, int cPlans, out State sChosen, ref List<Action> cPlan)
        {
            sChosen = null;
            List<State> lChosen = new List<State>();
            List<List<string>> lPlans = new List<List<string>>();

            for (int iPlan = 0; iPlan < cPlans; iPlan++)
            {
                State sCurrentChosen = null;
                List<string> lPlan = Plan(sPath, pssCurrent, out sCurrentChosen, ref cPlan);
                lPlans.Add(lPlan);
                lChosen.Add(sCurrentChosen);
                if (iPlan == 0)
                    sChosen = sCurrentChosen;
            }

            return ChooseMaximumLengthPrefix(lPlans);
        }

        private List<string> ChooseMaximumLengthPrefix(List<List<string>> lPlans)
        {
            List<List<string>> lCandidates = new List<List<string>>();
            foreach (List<string> lPlan in lPlans)
            {
                List<string> lClean = new List<string>();
                foreach (string sAction in lPlan)
                {
                    if (!sAction.StartsWith("merge") && !sAction.StartsWith("refute"))
                        lClean.Add(sAction);
                }
                lCandidates.Add(lClean);
            }
            int iCurrentAction = 0;
            while (lCandidates.Count > 1)
            {
                Dictionary<string, List<List<string>>> dActions = new Dictionary<string, List<List<string>>>();
                string sBestAction = "";
                foreach (List<string> lPlan in lCandidates)
                {

                    string sAction = "";
                    if (iCurrentAction < lPlan.Count)
                        sAction = lPlan[iCurrentAction];
                    if (!dActions.ContainsKey(sAction))
                        dActions[sAction] = new List<List<string>>();
                    dActions[sAction].Add(lPlan);
                    if (sBestAction == "" || dActions[sBestAction].Count < dActions[sAction].Count)
                        sBestAction = sAction;
                }
                if (sBestAction == "")
                    break;
                lCandidates = dActions[sBestAction];
                iCurrentAction++;
            }
            return lCandidates.First();
        }

        private List<string> RunPlannerNoFiles(MemoryStream msModels, int iIndex)
        {


            if (Planner != Planners.FF && Planner != Planners.FF_WSL)
                throw new NotImplementedException();

            Process p = new Process();
            FFProcesses[Thread.CurrentThread] = p;
            //p.StartInfo.WorkingDirectory = sPath;
            if (Planner == Planners.FF)
                p.StartInfo.FileName = Program.BASE_PATH + @"\Planners\ff.exe";
            if (Planner == Planners.FF_WSL)
            {
                p.StartInfo.WorkingDirectory = Program.BASE_PATH + @"\Planners\";
                p.StartInfo.FileName = @"C:\Windows\Sysnative\wsl.exe";
                //sWSL =  @"./ff";
                //sWSL = @"C:\Windows\System32\wsl.exe " + @"./ff";
                p.StartInfo.Arguments = @"./ff_wsl ";
            }
            //p.StartInfo.FileName = "C:\\Users\\lera\\Dropbox\\SDR\\Planners\\ff.exe";
            p.StartInfo.UseShellExecute = false;
            p.StartInfo.RedirectStandardOutput = true;
            p.StartInfo.RedirectStandardInput = true;
            p.StartInfo.RedirectStandardError = true;
            m_sFFOutput = "";
            p.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);
            p.ErrorDataReceived += new DataReceivedEventHandler(OutputHandler);

            /*
            StreamWriter sw = new StreamWriter(@"d:\temp\tmp_models.txt");
            msModels.Position = 0;
            StreamReader sr = new StreamReader(msModels);
            sw.Write(sr.ReadToEnd());
            sw.Close();
            */

            p.Start();
            p.BeginOutputReadLine();

            /*
            msModels.Position = 0; 
            StreamWriter swTest = new StreamWriter("D:/test.pddl");
            StreamReader srTest = new StreamReader(msModels);
            swTest.Write(srTest.ReadToEnd());
            swTest.Close();
            */

            msModels.Position = 0;
            BinaryReader srModels = new BinaryReader(msModels);

            while (srModels.PeekChar() >= 0)
                p.StandardInput.BaseStream.WriteByte(srModels.ReadByte());

            p.StandardInput.Close();

            if (!p.WaitForExit((int)PlannerTimeout.TotalMilliseconds))//2 minutes max
            {
                p.Kill();
                return null;
            }
            Thread.Sleep(50);
            List<string> lPlan = null;
            if (m_sFFOutput.Contains("found legal plan as follows"))
            {
                lPlan = new List<string>();
                string sPlan = m_sFFOutput.Substring(m_sFFOutput.IndexOf("found legal plan as follows"));
                string[] asPlan = sPlan.Split('\n');
                for (int i = 2; i < asPlan.Length; i++)
                {
                    if (!asPlan[i].Contains(":"))
                        break;
                    lPlan.Add(asPlan[i].Substring(asPlan[i].IndexOf(':') + 2).Trim().ToLower());
                }
            }
            //else
            //   Debug.WriteLine(m_sFFOutput);

            FFProcesses[Thread.CurrentThread] = null;
            return lPlan;
        }

        public List<string> RunPlanner(string sPath, MemoryStream msModel, int iIndex)
        {
            Debug.WriteLine("Calling underlying classical planner");

            if (SDRPlanner.Planner == Planners.LocalFSP)
            {
                ForwardSearchPlanner fsp = new ForwardSearchPlanner(msModel);
                Debug.WriteLine("Calling ForwardSearchPlanner");
                List<Action> lActions = fsp.Plan();
                Debug.WriteLine("ForwardSearchPlanner done. Plan:");
                List<string> lActionNames = new List<string>();
                foreach (Action a in lActions)
                {
                    Debug.WriteLine(a.Name);
                    lActionNames.Add(a.Name);
                }
                return lActionNames;
            }
            else
            {
                if (SDRPlanner.UseFilesForPlanners)
                {
                    if (!RunPlannerWithFiles(sPath, iIndex))
                        return null;
                    return ReadPlan(sPath);
                }
                else
                {
                    return RunPlannerNoFiles(msModel, iIndex);

                }
            }
        }





        private bool RunPlannerWithFiles(string sPath, int iIndex)
        {

            File.Delete(sPath + "plan.txt");
            File.Delete(sPath + "plan" + iIndex + ".txt");
            File.Delete(sPath + "mipsSolution.soln");
            File.Delete(sPath + "output.sas");
            File.Delete(sPath + "output");
            File.Delete(sPath + "sas_plan");

            if (Planner == Planners.FD)
                return RunFD(sPath, iIndex);

            Process p = new Process();
            FFProcesses[Thread.CurrentThread] = p;
            p.StartInfo.WorkingDirectory = sPath;

            if (Planner == Planners.FF_WSL)
            {
                p.StartInfo.FileName = @"C:\Windows\Sysnative\wsl.exe";
                //sWSL =  @"./ff";
                //sWSL = @"C:\Windows\System32\wsl.exe " + @"./ff";
                p.StartInfo.Arguments = @"./ff_wsl ";
            }

            if (Planner == Planners.FF)
                p.StartInfo.FileName = Program.BASE_PATH + @"\Planners\ff.exe";
            if (Planner == Planners.FFX)
                p.StartInfo.FileName = Program.BASE_PATH + @"\Planners\ff-x.exe";
            if (Planner == Planners.MIPS)
            {
                p.StartInfo.FileName = Program.BASE_PATH + @"\Planners\mips-xxl.exe";
                p.StartInfo.Arguments = "-O ";
            }
            if (Planner == Planners.FFsa)
                p.StartInfo.FileName = Program.BASE_PATH + @"\Planners\ffsa.exe";
            if (Planner == Planners.FFha)
                p.StartInfo.FileName = Program.BASE_PATH + @"\Planners\ffha.exe";
            if (Planner == Planners.MetricFF)
            {
                p.StartInfo.FileName = Program.BASE_PATH + @"\Planners\metric-ff.exe";
                p.StartInfo.Arguments = "-O ";
            }
            if (Planner == Planners.LPG)
            {
                p.StartInfo.FileName = Program.BASE_PATH + @"\Planners\lpg-td-1.0.exe";
                p.StartInfo.Arguments = "-n 1 ";
            }
            if (Planner == Planners.CPT)
            {
                p.StartInfo.FileName = Program.BASE_PATH + @"\Planners\cpt-1.0.exe";
                Program.RedirectShellOutput = true;
            }
            if (Planner == Planners.TRAPPER_WSL)
            {
                p.StartInfo.FileName = @"C:\Windows\Sysnative\wsl.exe";
                //sWSL =  @"./ff";
                //sWSL = @"C:\Windows\System32\wsl.exe " + @"./ff";
                p.StartInfo.Arguments = @"./trapper_wsl --domain Kd.pddl --problem Kp.pddl --search astar_trap --candidates a2";
            }
            else
            {
                if (iIndex != -1)
                    p.StartInfo.Arguments += "-o Kd" + iIndex + ".pddl -f Kp" + iIndex + ".pddl";
                else
                    p.StartInfo.Arguments += "-o Kd.pddl -f Kp.pddl";
            }

            if (Planner == Planners.FF_WSL || Planner == Planners.TRAPPER_WSL)
                p.StartInfo.Arguments += " > plan.txt";

            p.StartInfo.UseShellExecute = false;
            if (Program.RedirectShellOutput || Planner == Planners.FFX)
            {
                m_sFFOutput = "";
                p.StartInfo.RedirectStandardOutput = true;
                p.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);
            }
            p.Start();

            if (Program.RedirectShellOutput || Planner == Planners.FFX)
            {
                //string sOutput = p.StandardOutput.ReadToEnd();
                p.BeginOutputReadLine();
            }
            //p.WaitForExit();
            if (!p.WaitForExit((int)PlannerTimeout.TotalMilliseconds))//2 minutes max
            {
                p.Kill();
                return false;
            }
            Thread.Sleep(200);
            //p.StandardOutput.Close(); 
            FFProcesses[Thread.CurrentThread] = null;
            return true;
        }


        private List<string> readFDplan(string sPath)
        {
            List<string> lPlan = new List<string>();
            if (File.Exists(sPath + "sas_plan"))
            {
                StreamReader sr = new StreamReader(sPath + "sas_plan");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    sLine = sLine.Replace("(", "");
                    sLine = sLine.Replace(")", "");
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        sLine = sLine.Substring(iStart + 1).Trim();
                        lPlan.Add(sLine);
                    }
                    //else if (sLine.Count() > 0 && sLine.StartsWith(";"))
                    //{
                    //	lPlan.Add(sLine);
                    //}
                }
                sr.Close();
            }
            return lPlan;
        }


        private List<string> RunFDlannerWithFiles(string sPath, MemoryStream msModels, int iIndex)
        {

            File.Delete(sPath + "plan.txt");
            File.Delete(sPath + "plan" + iIndex + ".txt");
            File.Delete(sPath + "mipsSolution.soln");
            File.Delete(sPath + "output.sas");
            File.Delete(sPath + "output");
            File.Delete(sPath + "sas_plan");

            Process pFD = new Process();
            FFProcesses[Thread.CurrentThread] = pFD;
            //	p.StartInfo.WorkingDirectory = sPath;
            pFD.StartInfo.WorkingDirectory = sPath;


            pFD.StartInfo.FileName = @"C:\Users\OWNER\AppData\Local\Programs\Python\Python37-32\python.exe";

            pFD.StartInfo.Arguments += @"D:\Dropbox\NetworkAttack\projects\teacher-student-project\Planners\Fast-Downward-af6295c3dc9b\fast-downward.py";
            //pFD.StartInfo.Arguments += " --alias seq-sat-lama-2011";

            //if (iIndex > -1) 

            //p.StartInfo.Arguments += "-o kd.pddl -f kp" + iIndex + ".pddl -Z -O";
            if (iIndex == -2)
                pFD.StartInfo.Arguments += " dSupervisor.pddl pSupervisor.pddl ";
            else
                pFD.StartInfo.Arguments += " kd" + iIndex + ".pddl p.pddl";
            pFD.StartInfo.Arguments += " --search astar(lmcut())";
            pFD.StartInfo.UseShellExecute = false;
            pFD.StartInfo.RedirectStandardOutput = true;

            pFD.StartInfo.UseShellExecute = false;
            pFD.StartInfo.RedirectStandardOutput = true;
            pFD.StartInfo.RedirectStandardInput = true;
            m_sFFOutput = "";
            pFD.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);



            pFD.Start();
            pFD.BeginOutputReadLine();


            msModels.Position = 0;
            BinaryReader srModels = new BinaryReader(msModels);

            while (srModels.PeekChar() >= 0)
                pFD.StandardInput.BaseStream.WriteByte(srModels.ReadByte());

            pFD.StandardInput.Close();

            if (!pFD.WaitForExit((int)PlannerTimeout.TotalMilliseconds))//2 minutes max
            {
                pFD.Kill();
                return null;
            }
            pFD.WaitForExit();
            List<string> lPlan = null;
            if (m_sFFOutput.Contains("goal can be simplified to TRUE"))
            {
                return new List<string>();
            }
            if (m_sFFOutput.Contains("Solution found"))
            {
                lPlan = readFDplan(sPath);
            }
            else
            {
                lPlan = null;
            }
            FFProcesses[Thread.CurrentThread] = null;
            return lPlan;

        }


        public bool RunProcess(Process p, string sInputFile)
        {
            p.StartInfo.UseShellExecute = false;
            FFProcesses[Thread.CurrentThread] = p;
            if (Program.RedirectShellOutput)
            {
                p.StartInfo.RedirectStandardOutput = true;
                p.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);
            }
            if (sInputFile != null)
            {
                p.StartInfo.RedirectStandardInput = true;
            }

            p.Start();
            if (Program.RedirectShellOutput)
            {
                //string sOutput = p.StandardOutput.ReadToEnd();
                p.BeginOutputReadLine();
            }
            if (sInputFile != null)
            {
                StreamReader sr = new StreamReader(p.StartInfo.WorkingDirectory + "/" + sInputFile);
                StreamWriter sw = p.StandardInput;
                while (!sr.EndOfStream)
                    sw.WriteLine(sr.ReadLine());
                sr.Close();
                sw.Close();
            }

            //p.WaitForExit();
            if (!p.WaitForExit((int)PlannerTimeout.TotalMilliseconds))//2 minutes max
            {
                p.Kill();
                return false;
            }
            FFProcesses[Thread.CurrentThread] = null;
            return true;
        }

        public bool RunFD(string sPath, int iIndex)
        {
            Process p = new Process();
            p.StartInfo.WorkingDirectory = sPath;
            //p.StartInfo.FileName = Program.BASE_PATH + @"\PDDL\Planners\ff.exe";
            //p.StartInfo.FileName = @"D:\cygwin64\bin\bash.exe";
            //p.StartInfo.Arguments = @"D:\cygwin64\home\radimir\FastDownward\src\plan";
            p.StartInfo.FileName = @"C:\cygwin\bin\bash.exe";
            p.StartInfo.Arguments = @"C:\cygwin\home\shanigu\FastDownward\src\plan";
            if (iIndex != -1)
                p.StartInfo.Arguments += @" Kd" + iIndex + ".pddl Kp" + iIndex + ".pddl";
            else
                p.StartInfo.Arguments += @" Kd.pddl Kp.pddl";


            p.StartInfo.Arguments += " --heuristic \"hlm,hff=lm_ff_syn(lm_rhw(reasonable_orders=true,lm_cost_type=ONE,cost_type=ONE))\" " +
                                    " --search \"lazy_greedy([hff,hlm],preferred=[hff,hlm],cost_type=ONE)\"";
            //p.StartInfo.Arguments += " --heuristic \"hFF=ff(cost_type=1)\" " +
            //                       " --search \"lazy_greedy(hff, preferred=hff)\" ";
            if (!RunProcess(p, null))
                return false;

            return true;
        }


        private bool RunFDII(string sPath, int iIndex)
        {
            Process p = new Process();
            p.StartInfo.WorkingDirectory = sPath;
            //p.StartInfo.FileName = Program.BASE_PATH + @"\PDDL\Planners\ff.exe";
            p.StartInfo.FileName = @"C:\cygwin\bin\python.exe";

            if (iIndex != -1)
                p.StartInfo.Arguments = @" D:\cygwin64\home\radimir\FastDownward\src\translate\translate.py Kd" + iIndex + ".pddl Kp" + iIndex + ".pddl";
            else
                p.StartInfo.Arguments = @" D:\cygwin64\home\radimir\FastDownward\src\translate\translate.py Kd.pddl Kp.pddl";

            if (!RunProcess(p, null))
                return false;
            p = new Process();
            p.StartInfo.WorkingDirectory = sPath;
            //p.StartInfo.FileName = Program.BASE_PATH + @"\PDDL\Planners\ff.exe";
            p.StartInfo.FileName = @"D:\cygwin64\home\radimir\FastDownward\src\preprocess\preprocess.exe";
            if (!RunProcess(p, "output.sas"))
                return false;

            p = new Process();
            p.StartInfo.WorkingDirectory = sPath;
            //p.StartInfo.FileName = Program.BASE_PATH + @"\PDDL\Planners\ff.exe";
            /*
             --heuristic "hlm,hff=lm_ff_syn(lm_rhw(reasonable_orders=true,lm_cost_type=ONE,cost_type=ONE))"
             --search "lazy_greedy([hff,hlm],preferred=[hff,hlm],cost_type=ONE)"
             */
            p.StartInfo.FileName = @"D:\cygwin64\home\radimir\FastDownward\src\search\downward-1.exe";
            p.StartInfo.Arguments = " --heuristic \"hlm,hff=lm_ff_syn(lm_rhw(reasonable_orders=true,lm_cost_type=ONE,cost_type=ONE))\" " +
                                    " --search \"lazy_greedy([hff,hlm],preferred=[hff,hlm],cost_type=ONE)\"";
            //p.StartInfo.Arguments = " --heuristic \"hFF=ff(cost_type=1)\" " +
            //                       " --search \"lazy_greedy(hff, preferred=hff)\" ";
            if (!RunProcess(p, "output"))
                return false;

            return true;
        }
        private List<string> ReadPlanSimple(string sPlanFile)
        {
            List<string> lPlan = new List<string>();
            if (File.Exists(sPlanFile))
            {
                StreamReader sr = new StreamReader(sPlanFile);
                while (!sr.EndOfStream)
                {
                    string sAction = sr.ReadLine().Trim().ToLower();
                    if (sAction != "")
                        lPlan.Add(sAction);
                }
                sr.Close();
            }
            return lPlan;
        }
        private List<string> ReadPlan(string sPath)
        {
            List<string> lPlan = new List<string>();

            string sPlanFile = "plan.txt";
            if (Planner == Planners.FF_WSL)
            {
                if (File.Exists(sPath + sPlanFile))
                {
                    StreamReader sr = new StreamReader(sPath + sPlanFile);
                    bool bPlan = false;
                    bool bContainsPlan = false;
                    while (!sr.EndOfStream)
                    {
                        string sLine = sr.ReadLine().ToLower();
#if DEBUG
                        Debug.WriteLine(sLine);
#endif
                        if (sLine.Contains("time spent"))
                            bPlan = false;

                        if (bPlan)
                        {
                            int idx = sLine.IndexOf(":");
                            if (idx >= 0)
                            {
                                string sAction = sLine.Substring(idx + 1).Trim().ToLower();
                                if (sAction != "")
                                    lPlan.Add(sAction);
                            }
                        }

                        if (sLine.Contains("found legal plan as follows"))
                        {
                            bPlan = true;
                            bContainsPlan = true;
                        }
                    }
                    sr.Close();
                    if (!bContainsPlan)
                        return null;
                }
            }
            if (Planner == Planners.TRAPPER_WSL)
            {
                if (File.Exists(sPath + sPlanFile))
                {
                    using (StreamReader sr = new StreamReader(sPath + sPlanFile))
                    {
                        bool bPlan = false;
                        bool bContainsPlan = false;
                        while (!sr.EndOfStream)
                        {
                            string sLine = sr.ReadLine().ToLower();
#if DEBUG
                            Debug.WriteLine(sLine);
#endif
                            if (sLine.Contains("time:"))
                                bPlan = false;

                            if (bPlan)
                            {
                                int idx = sLine.IndexOf(".");
                                if (idx >= 0)
                                {
                                    string sAction = sLine.Substring(idx + 1).Trim().ToLower();
                                    if (sAction != "")
                                    {
                                        sAction = sAction.Substring(1, sAction.Length - 2);

                                        lPlan.Add(sAction);
                                    }
                                }
                            }

                            if (sLine.Contains("plan found with cost:"))
                            {
                                if (sLine.Contains("plan found with cost: 0"))
                                    bContainsPlan = false;
                                else
                                {
                                    bPlan = true;
                                    bContainsPlan = true;
                                }
                            }
                        }
                        sr.Close();
                        if (!bContainsPlan)
                            return null;
                    }
                }
            }
            else if (File.Exists(sPath + sPlanFile))
            {
                StreamReader sr = new StreamReader(sPath + sPlanFile);
                while (!sr.EndOfStream)
                {
                    string sAction = sr.ReadLine().Trim().ToLower();
                    if (sAction != "")
                        lPlan.Add(sAction);
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "mipsSolution.soln"))
            {
                StreamReader sr = new StreamReader(sPath + "mipsSolution.soln");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        int iEnd = sLine.IndexOf(")");
                        sLine = sLine.Substring(iStart + 1, iEnd - iStart - 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else if (File.Exists(sPath + "sas_plan"))
            {
                StreamReader sr = new StreamReader(sPath + "sas_plan");
                while (!sr.EndOfStream)
                {
                    string sLine = sr.ReadLine().Trim().ToLower();
                    sLine = sLine.Replace("(", "");
                    sLine = sLine.Replace(")", "");
                    if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                    {
                        int iStart = sLine.IndexOf("(");
                        sLine = sLine.Substring(iStart + 1).Trim();
                        lPlan.Add(sLine);
                    }
                }
                sr.Close();
            }
            else if (m_sFFOutput != null && m_sFFOutput != "")
            {
                string[] a = m_sFFOutput.Split('\n');
                bool bInPlan = false;
                foreach (string s in a)
                {
                    string sLine = s.Trim().ToLower();
                    if (sLine.Contains("goal") && sLine.Contains("not reachable"))
                        return null;
                    if (sLine.Contains("------------") || sLine.Contains("found legal plan") || sLine.Contains("time spent"))
                    {
                        bInPlan = !bInPlan;
                    }
                    else
                    {
                        if (bInPlan)
                        {
                            if (sLine.Count() > 0 && !sLine.StartsWith(";"))
                            {
                                sLine = sLine.Replace("(", "");
                                sLine = sLine.Replace(")", "");
                                int iStart = sLine.IndexOf(":");
                                sLine = sLine.Substring(iStart + 1).Trim();
                                lPlan.Add(sLine);
                            }
                        }
                    }
                }
            }
            else
                return null;

            List<string> lFilteredPlan = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.Contains("-remove") ||
                    sAction.Contains("-translate"))
                    continue;
                if (sAction.Contains("-add"))
                    lFilteredPlan.Add(sAction.Replace("-add", ""));
                else
                    lFilteredPlan.Add(sAction);

            }

            return lFilteredPlan;
        }

        static bool bFirst = true;


        private List<string> Plan(string sPath, string deadEndFile, PartiallySpecifiedState pssCurrent, Predicate pObserve, out State sChosen)
        {
            DirectoryInfo di = new DirectoryInfo(sPath);
            foreach (FileInfo fi in di.GetFiles())
                if ((fi.Name.StartsWith("Kd") || fi.Name.StartsWith("Kp")) && fi.Name.EndsWith(".pddl"))
                    fi.Delete();
            int cTags = 0;

            CompoundFormula cfGoal = new CompoundFormula("or");
            cfGoal.AddOperand(pssCurrent.Problem.Goal);
            if (pObserve != null)
            {
                cfGoal.AddOperand(pObserve);
            }
            MemoryStream msModels = null;
            sChosen = pssCurrent.WriteTaggedDomainAndProblem(sPath + "Kd.pddl", sPath + "Kp.pddl", cfGoal, out cTags, out msModels);

            MemoryStream msPlan = null;
            List<string> lPlan = null;
            lPlan = RunPlanner(sPath, msModels, -1);
            if (lPlan == null)
            {
                Debug.WriteLine("FF failed to meet timeout");
                return null;
            }


#if DEBUG
            if (lPlan == null || lPlan.Count == 0)
                Debug.WriteLine("BUGBUG");
            else if (!WriteAllKVariations && UseFilesForPlanners)
                VerifyPlan(sPath, deadEndFile, lPlan);
#endif
            return lPlan;
        }


        private List<string> Plan(string sPath, string deadEndFile, PartiallySpecifiedState pssCurrent, PartiallySpecifiedState pssClosed, out State sChosen)
        {
            DirectoryInfo di = new DirectoryInfo(sPath);
            foreach (FileInfo fi in di.GetFiles())
                if ((fi.Name.StartsWith("Kd") || fi.Name.StartsWith("Kp")) && fi.Name.EndsWith(".pddl"))
                    fi.Delete();
            int cTags = 0;

            CompoundFormula cfGoal = new CompoundFormula("or");
            cfGoal.AddOperand(pssCurrent.Problem.Goal);
            if (pssClosed != null)
            {
                CompoundFormula cfAnd = new CompoundFormula("and");
                foreach (GroundedPredicate gp in pssClosed.Observed)
                {
                    if (!pssCurrent.Problem.InitiallyUnknown(gp) && !pssCurrent.Problem.Domain.AlwaysConstant(gp))
                    {
                        if (!pssCurrent.Observed.Contains(gp))
                            cfAnd.AddOperand(gp);
                    }
                }
                if (cfAnd.Operands.Count > 0)
                    cfGoal.AddOperand(cfAnd);
            }
            MemoryStream msModels = null;
            sChosen = pssCurrent.WriteTaggedDomainAndProblem(sPath + "Kd.pddl", sPath + "Kp.pddl", cfGoal, out cTags, out msModels);

            MemoryStream msPlan = null;
            List<string> lPlan = null;
            lPlan = RunPlanner(sPath, msModels, -1);
            if (lPlan == null)
            {
                Debug.WriteLine("FF failed to meet timeout");
                return null;
            }


#if DEBUG
            if (lPlan == null || lPlan.Count == 0)
                Debug.WriteLine("BUGBUG");
            else if (!WriteAllKVariations && UseFilesForPlanners)
                VerifyPlan(sPath, deadEndFile, lPlan);
#endif
            return lPlan;
        }

        private List<string> GetImmediatePlan(PartiallySpecifiedState pssCurrent)
        {
            return null;
            List<string> lPlan = null;
            List<Action> lActuationActions = pssCurrent.Problem.Domain.GroundAllActuationActions(pssCurrent.Observed, true);
            foreach (Action a in lActuationActions)
            {
                PartiallySpecifiedState pssNext = pssCurrent.Apply(a, out Formula fObserve);
                if (pssNext != null && pssNext.IsGoalState())
                {
                    lPlan = new List<string>();
                    lPlan.Add(a.Name);
                    return lPlan;
                }
            }
            return null;
        }

        private List<string> PlanToObserveDeadEnd(string sPath, string deadEndFile, PartiallySpecifiedState pssCurrent, List<Formula> lMaybeDeadends,
            bool bPreconditionFailure, out State sChosen, ref List<Action> cPlan)
        {
            Debug.WriteLine("Started classical deadend aware planning");

            List<string> lPlan = null;
            if (TryImmediatePlan)
            {
                lPlan = GetImmediatePlan(pssCurrent);
                if (lPlan != null)
                {
                    sChosen = null;
                    return lPlan;
                }
            }



            DirectoryInfo di = new DirectoryInfo(sPath);

            bool bDone = false;
            while (!bDone)
            {
                try
                {
                    foreach (FileInfo fi in di.GetFiles())
                        if ((fi.Name.StartsWith("Kd") || fi.Name.StartsWith("Kp")) && fi.Name.EndsWith(".pddl"))
                            fi.Delete();
                    bDone = true;
                }
                catch (IOException e)
                {

                }
            }
            int cTags = 0;
            //sPath = @"D:\Research\projects\PDDL\CLG_benchmarks\PDDLs\";
            //sChosen = pssCurrent.WriteTaggedDomainAndProblem(sPath + "Kd." + pssCurrent.Problem.Name + "..pddl", sPath + "Kp." + pssCurrent.Problem.Name + "..pddl", out cTags);
            MemoryStream msModels = null;
            sChosen = pssCurrent.WriteTaggedDomainAndProblemDeadEnd(sPath + "Kd.pddl", sPath + "Kp.pddl", lMaybeDeadends, DeadendStrategy, bPreconditionFailure, out cTags, out msModels);
            //sChosen = pssCurrent.WriteTaggedDomainAndProblemDeadEnd(sPath + "Kd.pddl", sPath + "Kp.pddl", maybeDeadEnd, ActiveStrategyDeadEnds,  out cTags, out msModels);
            MemoryStream msPlan = null;

            if (false)
                lPlan = ManualSolve(sPath);

            if (!WriteAllKVariations || cTags == 1)
            {
                lPlan = RunPlanner(sPath, msModels, -1);
                if (lPlan == null)
                {
                    Debug.WriteLine("FF failed");
                    //lPlan = ManualSolve(sPath);
                    return null;
                }

            }
            else
            {
                List<List<string>> lPlans = new List<List<string>>();
                for (int i = 0; i < cTags; i++)
                {
                    lPlan = RunPlanner(sPath, msModels, i);
                    if (msPlan == null)
                    {
                        //throw new Exception("FF failed to meet timeout");
                        Debug.WriteLine("FF failed to meet timeout");
                        return null;
                    }
                    else
                        lPlans.Add(lPlan);
                }

                List<string> lJointPlan = ComputeSensingPrefix(lPlans, pssCurrent.Problem.Domain);
                if (lJointPlan.Count == 0)
                {//learn to distinguish between states
                    lPlan = RunPlanner(sPath, msModels, cTags);
                    if (lPlan == null)
                    {
                        //throw new Exception("FF failed to meet timeout");
                        Debug.WriteLine("FF failed to meet timeout");
                        return null;
                    }
                }
                else
                    lPlan = lJointPlan;
            }


#if DEBUG
            if (lPlan == null || lPlan.Count == 0)
            {
                Debug.WriteLine("BUGBUG");
                ManualSolve(sPath);
                lPlan = RunPlanner(sPath, msModels, -1);

            }

            // else if (!WriteAllKVariations && UseFilesForPlanners)
            //    VerifyPlan(sPath, deadEndFile, lPlan);
#endif
            return lPlan;


        }

        int c = 0;

        private void DeletePreviousFiles(string sPath)
        {
            DirectoryInfo di = new DirectoryInfo(sPath);
            bool bDone = false;
            while (!bDone)
            {
                try
                {
                    foreach (FileInfo fi in di.GetFiles())
                        if ((fi.Name.StartsWith("Kd") || fi.Name.StartsWith("Kp")) && fi.Name.EndsWith(".pddl"))
                            fi.Delete();
                    bDone = true;
                }
                catch (IOException e)
                {

                }
            }
        }

        private List<string> Plan(string sPath, PartiallySpecifiedState pssCurrent, out State sChosen, ref List<Action> cPlan)
        {
            Debug.WriteLine("Started classical planning");
            List<string> lPlan = null;
            if (TryImmediatePlan)
            {
                lPlan = GetImmediatePlan(pssCurrent);
                if (lPlan != null)
                {
                    sChosen = null;
                    return lPlan;
                }
            }

            DeletePreviousFiles(sPath);

            int cTags = 0;
            MemoryStream msModels = null;
            sChosen = pssCurrent.WriteTaggedDomainAndProblem(sPath + "Kd.pddl", sPath + "Kp.pddl", out cTags, out msModels);
            c++;
            if (false)
            {
                //Current problem - not clear how we can identify the problematic line - 
                //it seems that (affected ?x) applies to all devices on their way to the device, and thus we can distinguish between them
                //idea - try to connect the suspected problematic line to the other side
                return ManualSolve(sPath);
            }
            MemoryStream msPlan = null;

            if (!WriteAllKVariations || cTags == 1)
            {
                lPlan = RunPlanner(sPath, msModels, -1);
                if (lPlan == null)
                {
                    Debug.WriteLine("FF failed to meet timeout");
                    //ManualSolve(sPath);
                    return null;
                }


            }
            else
            {
                List<List<string>> lPlans = new List<List<string>>();
                for (int i = 0; i < cTags; i++)
                {
                    lPlan = RunPlanner(sPath, msModels, i);
                    if (msPlan == null)
                    {
                        //throw new Exception("FF failed to meet timeout");
                        Debug.WriteLine("FF failed to meet timeout");
                        return null;
                    }
                    else
                        lPlans.Add(lPlan);
                }

                List<string> lJointPlan = ComputeSensingPrefix(lPlans, pssCurrent.Problem.Domain);
                if (lJointPlan.Count == 0)
                {//learn to distinguish between states
                    lPlan = RunPlanner(sPath, msModels, cTags);
                    if (lPlan == null)
                    {
                        //throw new Exception("FF failed to meet timeout");
                        Debug.WriteLine("FF failed to meet timeout");
                        return null;
                    }
                }
                else
                    lPlan = lJointPlan;
            }


#if DEBUG
            if (lPlan == null || lPlan.Count == 0)
            {
                Debug.WriteLine("BUGBUG");
            }

            // else if(!WriteAllKVariations && UseFilesForPlanners)
            //    VerifyPlan(sPath, deadEndFile,  lPlan);
#endif
            return lPlan;
        }

        private List<string> PlanWithClassicalDeadendDetection(string sPath, PartiallySpecifiedState pssCurrent, out State sChosen, ref List<Action> cPlan, out bool bIsDeadend)
        {
            Debug.WriteLine("Started classical planning");
            List<string> lPlan = null;
            bIsDeadend = false;

            sChosen = null;


            DeletePreviousFiles(sPath);

            bool bFoundSolvableState = false;

            while (!bFoundSolvableState)
            {
                bFoundSolvableState = true;
                int cTags = 0;
                MemoryStream msModels = null;
                sChosen = pssCurrent.WriteTaggedDomainAndProblem(sPath + "Kd.pddl", sPath + "Kp.pddl", out cTags, out msModels);

                if (sChosen == null)
                {
                    bIsDeadend = true;
                    return null;
                }

                if (false)
                {
                    lPlan = ManualSolve(sPath);
                }

                lPlan = RunPlanner(sPath, msModels, -1);
                if (lPlan == null)
                {
                    if (pssCurrent.Hidden.Count() == 0)
                    {
                        bIsDeadend = true;
                        return null;
                    }
                    else
                    {
                        bFoundSolvableState = false;
                        pssCurrent.AddCurrentToDeadendTags();
                    }
                }
            }


#if DEBUG
            if (lPlan == null || lPlan.Count == 0)
            {
                Debug.WriteLine("BUGBUG");
            }

#endif
            return lPlan;
        }



        private static List<string> ManualSolve(string sPath)
        {
            Parser parser = new Parser();
            Domain dK = parser.ParseDomain(sPath + "Kd.pddl");
            Problem pK = parser.ParseProblem(sPath + "Kp.pddl", "", dK);

            BFSSolver solver = new BFSSolver();
            //LandmarkSolver solver = new LandmarkSolver();
            //solver.IdentifyLandmarks(pK, dK);
            List<Action> lActions = solver.ManualSolve(pK, dK, true);

            //ForwardSearchPlanner solver = new ForwardSearchPlanner(dK, pK, new HSPHeuristic(dK, pK.Goal, false));
            //List<Action> lActions = solver.Plan(pK.GetInitialBelief().ChooseState(false));
            List<string> lActionNames = new List<string>();
            foreach (Action a in lActions)
            {
                if (a != null)
                    lActionNames.Add(a.Name.Replace("_", " "));
            }
            bFirst = false;
            return lActionNames;
        }

        private double ComputePlanSimilarity(List<string> lPlan1, List<string> lPlan2)
        {
            int i = 0;
            double cIntersection = 0;
            foreach (string sAction in lPlan1)
                if (lPlan2.Contains(sAction))
                    cIntersection++;
            return cIntersection / (lPlan1.Count + lPlan2.Count - cIntersection);
        }

        private double ComputePlanSimilarity(List<List<string>> lPlans)
        {
            double dMinSimilarity = 1.0;
            for (int i = 0; i < lPlans.Count - 1; i++)
            {
                for (int j = i + 1; j < lPlans.Count; j++)
                {
                    double dSim = ComputePlanSimilarity(lPlans[i], lPlans[j]);
                    if (dSim < dMinSimilarity)
                        dMinSimilarity = dSim;
                }
            }
            return dMinSimilarity;
        }

        private List<string> ComputeJointPrefix(List<List<string>> lPlans, Domain d)
        {
            List<string> lJointPrefix = new List<string>();
            List<List<string>> lPlansSuffix = new List<List<string>>();
            foreach (List<string> lPlan in lPlans)
                lPlansSuffix.Add(FilterReasoningActions(lPlan));
            string sCurrentAction = "";
            while (lPlansSuffix[0].Count > 0)
            {
                sCurrentAction = lPlansSuffix[0][0];
                bool bAllAgree = true;
                for (int i = 1; i < lPlansSuffix.Count; i++)
                {
                    if (lPlansSuffix[i][0] != sCurrentAction)
                        bAllAgree = false;
                }
                if (bAllAgree)
                {
                    lJointPrefix.Add(sCurrentAction);
                    foreach (List<string> lPlan in lPlansSuffix)
                        lPlan.RemoveAt(0);
                }
                else
                    break;
            }
            //now add all immediate sensing actions
            foreach (List<string> lPlan in lPlansSuffix)
            {
                int iCurrent = 0;
                while (d.IsObservationAction(lPlan[iCurrent]))
                {
                    if (!lJointPrefix.Contains(lPlan[iCurrent]))
                        lJointPrefix.Add(lPlan[iCurrent]);
                    iCurrent++;
                }
            }

            return lJointPrefix;
        }

        private List<string> ComputeSensingPrefix(List<List<string>> lPlans, Domain d)
        {
            List<string> lJointPrefix = new List<string>();
            List<List<string>> lPlansSuffix = new List<List<string>>();
            foreach (List<string> lPlan in lPlans)
                lPlansSuffix.Add(FilterReasoningActions(lPlan));
            SameAction sa = new SameAction();

            List<string> lFirstSensingPlan = null, lShortestPlan = null;
            int iFirstSensingAction = -1;
            int iAction = 0;
            int cPlans = lPlansSuffix.Count;
            for (iAction = 0; cPlans > 0 && lFirstSensingPlan == null; iAction++)
            {
                foreach (List<string> lPlan in lPlansSuffix)
                {
                    if (lPlan.Count == iAction)
                    {
                        if (lShortestPlan == null)
                            lShortestPlan = lPlan;
                        cPlans--;
                    }
                    if (iAction < lPlan.Count && d.IsObservationAction(lPlan[iAction]))
                    {
                        iFirstSensingAction = iAction;
                        lFirstSensingPlan = lPlan;
                    }
                }
            }
            if (lFirstSensingPlan == null)
                lFirstSensingPlan = lShortestPlan;
            if (iFirstSensingAction == -1)
                iFirstSensingAction = lFirstSensingPlan.Count;


            for (iAction = 0; iAction < iFirstSensingAction; iAction++)
            {
                List<List<string>> lNewSuffixes = new List<List<string>>();
                foreach (List<string> lPlan in lPlansSuffix)
                {
                    if (sa.Equals(lPlan[iAction], lFirstSensingPlan[iAction]))
                        lNewSuffixes.Add(lPlan);
                }
                lJointPrefix.Add(lFirstSensingPlan[iAction]);
                lPlansSuffix = lNewSuffixes;
            }
            foreach (List<string> lPlan in lPlansSuffix)
            {
                for (iAction = iFirstSensingAction; iAction < lPlan.Count; iAction++)
                {
                    if (d.IsObservationAction(lPlan[iAction]))
                    {
                        if (!lJointPrefix.Contains(lPlan[iAction]))
                            lJointPrefix.Add(lPlan[iAction]);
                    }
                    else
                        break;
                }
            }

            return lJointPrefix;
        }

        private List<string> ComputeVotingPrefix(List<List<string>> lPlans, Domain d)
        {
            List<string> lJointPrefix = new List<string>();
            List<List<string>> lPlansSuffix = new List<List<string>>();
            foreach (List<string> lPlan in lPlans)
                lPlansSuffix.Add(FilterReasoningActions(lPlan));
            string sCurrentAction = "";
            SameAction sa = new SameAction();
            while (lPlansSuffix.Count >= lPlans.Count / 2 && lPlansSuffix[0].Count > 0)
            {
                bool bFoundObservationAction = false;
                Dictionary<string, int> dVotes = new Dictionary<string, int>(sa);
                foreach (List<string> lPlan in lPlansSuffix)
                {
                    if (lPlan.Count > 0)
                    {
                        while (d.IsObservationAction(lPlan[0]))
                        {
                            if (!lJointPrefix.Contains(lPlan[0]))
                            {
                                lJointPrefix.Add(lPlan[0]);
                            }
                            bFoundObservationAction = true;
                            lPlan.RemoveAt(0);
                        }
                        sCurrentAction = lPlan[0];
                        if (!dVotes.ContainsKey(sCurrentAction))
                            dVotes[sCurrentAction] = 0;
                        dVotes[sCurrentAction]++;
                    }
                }
                if (bFoundObservationAction)
                    break;
                string sMaxAction = dVotes.Keys.First();
                foreach (KeyValuePair<string, int> p in dVotes)
                {
                    if (p.Value > dVotes[sMaxAction])
                        sMaxAction = p.Key;
                }
                lJointPrefix.Add(sMaxAction);
                List<List<string>> lNewSuffixes = new List<List<string>>();
                foreach (List<string> lPlan in lPlansSuffix)
                {
                    if (lPlan.Count > 0 && sa.Equals(lPlan[0], sMaxAction))
                    {
                        lPlan.RemoveAt(0);
                        lNewSuffixes.Add(lPlan);
                    }
                }
                lPlansSuffix = lNewSuffixes;
            }
            return lJointPrefix;
        }

        private class SameAction : IEqualityComparer<string>
        {

            #region IEqualityComparer<string> Members

            public bool Equals(string s1, string s2)
            {
                int iTag1Index = s1.IndexOf("-kw-tag") + 7;
                string s1Tag = s1.Substring(iTag1Index, 1).Trim();
                s1 = s1.Replace("-kw-tag" + s1Tag, "");
                int iTag2Index = s2.IndexOf("-kw-tag") + 7;
                string s2Tag = s2.Substring(iTag2Index, 1).Trim();
                s2 = s2.Replace("-kw-tag" + s2Tag, "");
                return s1 == s2;
            }

            public int GetHashCode(string obj)
            {
                return obj.Substring(0, obj.IndexOf("-")).GetHashCode();
            }

            #endregion
        }

        private List<string> FilterReasoningActions(List<string> lPlan)
        {
            List<string> lFiltered = new List<string>();
            foreach (string sAction in lPlan)
            {
                if (sAction.StartsWith("merge") || sAction.StartsWith("unmerge") || sAction.StartsWith("tagrefute") || sAction.StartsWith("tagmerge") || sAction.StartsWith("refute"))
                    continue;
                if (sAction.EndsWith("-t") || sAction.EndsWith("-f"))
                    lFiltered.Add(sAction.Substring(sAction.Length - 2));
                else if (sAction.Contains("-t "))
                    lFiltered.Add(sAction.Replace("-t ", " "));
                else if (sAction.Contains("-f "))
                    lFiltered.Add(sAction.Replace("-f ", " "));
                else
                    lFiltered.Add(sAction);
            }
            return lFiltered;
        }

        private string m_sFFOutput;
        private void OutputHandler(object sendingProcess, DataReceivedEventArgs outLine)
        {
            m_sFFOutput += outLine.Data + "\n";
            Debug.WriteLine(outLine.Data);
        }

        private void VerifyPlan(string sPath, string deadEndFile, List<string> lPlan)
        {
            Parser p = new Parser();
            Domain domain = p.ParseDomain(sPath + "Kd.pddl");
            Problem problem = p.ParseProblem(sPath + "Kp.pddl", deadEndFile, domain);
            State sInit = problem.GetInitialBelief().ChooseState(true);
            State sCurrent = sInit, sNext = null;
            for (int i = 0; i < lPlan.Count; i++)
            {
                string sAction = lPlan[i];
                sNext = sCurrent.Apply(sAction);
                if (sNext == null)
                {
                    Debug.WriteLine("BUGBUG");
                    sNext = sCurrent.Apply(sAction);
                    return;
                }
                sCurrent = sNext;
            }
            if (!problem.IsGoalState(sCurrent))
                Debug.WriteLine("Plan verification failed!");
        }

        TimeSpan tsInPlanning = new TimeSpan();
        //static int iSeed = 0;

        public Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> alreadyVisitedStates = null;
        public void OfflinePlanning(string sPath, string deadEndFile, Domain domain, Problem problem, out TimeSpan tsTotal, out int cPlanning, out int iPolicySize, out bool bValid)
        {
            Console.WriteLine("Started offline planning for " + domain.Name + ", " + DateTime.Now);

            alreadyVisitedStates = new Dictionary<PartiallySpecifiedState, PartiallySpecifiedState>(new PartiallySpecifiedState_IEqualityComparer());
            int nextId = 1;
            DateTime dtStart = DateTime.Now;
            BeliefState bsInitial = problem.GetInitialBelief();
            //if (bsInitial.AvailableActions.Count==0) throw new Exception("Can not create initial belief state!");
            Stack<PartiallySpecifiedState> stateStack = new Stack<PartiallySpecifiedState>();
            int cActions = 0;
            cPlanning = 0;
            List<PartiallySpecifiedState> lClosedStates = new List<PartiallySpecifiedState>();
            State sChosen = null;
            bool bGoalReached = false;
            bool bDone = false;
            PartiallySpecifiedState pssInitial = bsInitial.GetPartiallySpecifiedState();

            pssInitial.mayChanged = new HashSet<Predicate>();
            pssInitial.ActionsWithConditionalEffect = new HashSet<Action>();

            //    pssInitial.MinMishapCount = 2;
            // pssInitial.MishapType = false;
            stateStack.Push(pssInitial);
            PartiallySpecifiedState pssCurrent = null;
            List<List<string>> lExecutedPlans = new List<List<string>>();
            List<PartiallySpecifiedState> lGoalStates = new List<PartiallySpecifiedState>();
            //Dictionary<GroundedPredicate, Dictionary<PartiallySpecifiedState, List<Action>>> dFinalPlans = new Dictionary<GroundedPredicate, Dictionary<PartiallySpecifiedState, List<Action>>>();
            int counter = 0;
            int cFoundClosedStates = 0, cFoundOpenStates = 0;
            Formula fObserved = null;

            bool bPreconditionFailure = false;
            Action aFailedPreconditionAction = null;


            while (!bDone)
            {

                if (lExecutedPlans.Count > 5)
                {
                    bool bSuspectedLoop = false;
                    List<string> lLast = lExecutedPlans[lExecutedPlans.Count - 1];
                    for (int i = 2; i < 5; i++)
                    {
                        bool bSame = true;
                        List<string> l = lExecutedPlans[lExecutedPlans.Count - i];
                        if (lLast.Count == l.Count)
                        {
                            for (int j = 0; j < lLast.Count && bSame; j++)
                            {
                                if (l[j] != lLast[j])
                                    bSame = false;
                            }
                        }
                        else
                            bSame = false;
                        if (bSame)
                        {
                            bSuspectedLoop = true;
                            break;
                        }
                    }
                    if (bSuspectedLoop)
                    {
                        TagsCount++;
                    }
                    else
                    {
                        if (TagsCount > 2)
                            TagsCount--;
                    }
                }

                if (stateStack.Count == 0)
                {
                    bDone = true;
                    break;
                }
                else
                {
                    pssCurrent = stateStack.Pop();
                }


                bool bStateHandled = false;
                if (pssCurrent.IsClosedState(lClosedStates))
                {
                    Debug.WriteLine("Found closed state");

                    pssCurrent.UpdateClosedStates(lClosedStates, alreadyVisitedStates, domain);
                    cFoundClosedStates++;
                    if (stateStack.Count == 0)
                    {
                        bDone = true;
                    }
                    bStateHandled = true;
                }
                else if (pssCurrent.AlreadyVisited(alreadyVisitedStates))
                {
                    cFoundOpenStates++;
                    PartiallySpecifiedState psIdentical = alreadyVisitedStates[pssCurrent];
                    pssCurrent.UpdateClosedStates(pssCurrent.Predecessor, lClosedStates, alreadyVisitedStates, domain);
                    if (stateStack.Count == 0)
                    {
                        bDone = true;
                    }
                    bStateHandled = true;
                }
                else
                {


                    if (SDR_OBS)
                    {
                        List<Action> lObservationActions = bsInitial.Problem.Domain.GroundAllObservationActions(pssCurrent.Observed, true);
                        foreach (Action a in lObservationActions)
                        {
                            Predicate pObserve = ((PredicateFormula)a.Observe).Predicate;
                            if (!pssCurrent.Observed.Contains(pObserve) && !pssCurrent.Observed.Contains(pObserve.Negate()))
                            {
                                pssCurrent.ApplyOffline(a, out bool bObservationPreconditionFailed, out fObserved, out PartiallySpecifiedState psTrueState, out PartiallySpecifiedState psFalseState);
                                if (psTrueState != null && psFalseState != null)
                                {
                                    stateStack.Push(psTrueState);
                                    pssCurrent = psFalseState;
                                }
                            }
                        }
                    }


                }
                List<string> lPlan = null;
                List<Action> cPlan = null;

                if (!bStateHandled)
                {
                    while (lPlan == null || lPlan.Count == 0)
                    {
                        Debug.Write("Checking state " + pssCurrent.ToString() + " |P|=" + cPlanning + " |A|=" + cActions + " T=" + ((long)(DateTime.Now - dtStart).TotalSeconds)
                            + " |C|=" + PartiallySpecifiedState.ClosedStates
                            //+ " |TC|=" + PartiallySpecifiedState.MaxTreeSize
                            );

                        //lPlan = null; 
                        DateTime dtBefore = DateTime.Now;
                        cPlanning++;
                        lPlan = null;



                        if (lPlan == null)
                        {

                            if (DeadendStrategy == DeadendStrategy.Classical)
                            {
                                bool bIsDeadEnd = false;
                                lPlan = PlanWithClassicalDeadendDetection(sPath, pssCurrent, out sChosen, ref cPlan, out bIsDeadEnd);
                                if (bIsDeadEnd)
                                {
                                    HashSet<Predicate> hsDeadend = new HashSet<Predicate>();
                                    hsDeadend.Add(Domain.FALSE_PREDICATE);
                                    pssCurrent.UpdateClosedStates(lClosedStates, alreadyVisitedStates, domain, hsDeadend);
                                    cFoundClosedStates++;
                                    if (stateStack.Count == 0)
                                    {
                                        bDone = true;
                                        break;
                                    }
                                    closeDead = true;
                                    pssCurrent = stateStack.Pop();
                                    continue;
                                }
                            }
                            else
                            {
                                maybeDead = false;
                                closeDead = false;

                                List<Formula> lDeadends = null;
                                Debug.WriteLine(pssCurrent);
                                DeadEndExistence isDeadEnd = pssCurrent.IsDeadEndExistenceAll(out lDeadends);
                                if (isDeadEnd == DeadEndExistence.MaybeDeadEnd)
                                {
                                    if (randomState == false)
                                    {
                                        maybeDead = true;
                                        //Formula resuceDeadEnd = daedend.Reduce(pssCurrent.m_lObserved);

                                        lPlan = PlanToObserveDeadEnd(sPath, deadEndFile, pssCurrent, lDeadends, bPreconditionFailure, out sChosen, ref cPlan);
                                        break;
                                    }

                                }

                                if (isDeadEnd == DeadEndExistence.DeadEndTrue)
                                {
                                    HashSet<Predicate> deadList = new HashSet<Predicate>();


                                    foreach (Formula fDeadend in lDeadends)
                                    {
                                        if (fDeadend is CompoundFormula)
                                        {

                                            fDeadend.GetAllPredicates(deadList);
                                        }
                                        else
                                        {

                                            PredicateFormula pf = (PredicateFormula)fDeadend;
                                            deadList.Add(pf.Predicate);


                                        }
                                    }

                                    pssCurrent.UpdateClosedStates(lClosedStates, alreadyVisitedStates, domain, deadList);
                                    cFoundClosedStates++;
                                    if (stateStack.Count == 0)
                                    {
                                        bDone = true;
                                        break;
                                    }

                                    closeDead = true;

                                }




                                if (maybeDead == false && closeDead)
                                {
                                    pssCurrent = stateStack.Pop();
                                    continue;

                                }




                                if (lPlan == null && maybeDead == false && closeDead == false)
                                {
                                    lPlan = Plan(sPath, pssCurrent, out sChosen, ref cPlan);
                                }
                            }
                        }
                        tsInPlanning += DateTime.Now - dtBefore;
                        if (lPlan == null)
                            throw new Exception("Failed to plan for current state");
                    }

                    PartiallySpecifiedState pssPlanState = pssCurrent;

                    counter++;

                    if (lPlan != null)
                    {
                        lExecutedPlans.Add(new List<string>());
                        int actionIndex = -1;
                        foreach (string sAction in lPlan)
                        {
                            actionIndex++;
                            if (!IsReasoningAction(sAction.ToLower()))
                            {
                                PartiallySpecifiedState psTrueState, psFalseState;
                                lExecutedPlans.Last().Add(sAction);
                                Action a = null;



                                if (pssCurrent.IsClosedState(lClosedStates))
                                {
                                    Debug.WriteLine("close state entry" + pssCurrent);
                                    //Debug.WriteLine("Closed state found " + pssCurrent);
                                    cFoundClosedStates++;
                                    pssCurrent.UpdateClosedStates(lClosedStates, alreadyVisitedStates, domain);
                                    pssCurrent = null;
                                    break;
                                }


                                if (pssCurrent.AlreadyVisited(alreadyVisitedStates))
                                {
                                    //Debug.WriteLine("Visited state found " + pssCurrent.ID + " == " + alreadyVisitedStates[pssCurrent].ID);
                                    PartiallySpecifiedState psIdentical = alreadyVisitedStates[pssCurrent];
                                    pssCurrent.UpdateClosedStates(pssCurrent.Predecessor, lClosedStates, alreadyVisitedStates, domain);
                                    cFoundOpenStates++;
                                    pssCurrent = null;
                                    break;
                                }


                                pssCurrent.ApplyOffline(sAction, out a, out bPreconditionFailure, out fObserved, out psTrueState, out psFalseState);
                                Debug.WriteLine("Executing: " + sAction);



                                //if (a.Observe != null && ((psTrueState != null && psFalseState == null) || (psTrueState == null && psFalseState != null)))
                                //  Debug.Write("dd");

                                if (psTrueState == null && psFalseState == null)
                                {
                                    if (bPreconditionFailure)
                                    {
                                        Debug.WriteLine("Precondition failure");
                                        stateStack.Push(pssCurrent);
                                        pssCurrent = null;
                                        break;
                                    }
                                    //else - observation action for something that is already known - continue with the same state
                                }
                                else
                                {
                                    // if (pssCurrent.ID == 59 || (psTrueState != null && psTrueState.ID == 59) || (psFalseState != null && psFalseState.ID == 59))
                                    //   Debug.Write("dd");
                                    pssCurrent.MarkVisited(alreadyVisitedStates);

                                    //Debug.WriteLine(pssCurrent.ID + "=>" + psTrueState.ID);

                                    /***********************************************************************************
                                    StreamWriter swChildren = new StreamWriter("children.txt", true);
                                    swChildren.WriteLine(pssCurrent.ID + ", " + psTrueState.ID + ", " + psTrueState.GeneratingAction.Name + ", " + psTrueState.GeneratingObservation);
                                    if(psFalseState != null)
                                        swChildren.WriteLine(pssCurrent.ID + ", " + psFalseState.ID + ", " + psFalseState.GeneratingAction.Name + ", " + psFalseState.GeneratingObservation);
                                    swChildren.Close();
                                    /***********************************************************************************/

                                    if (psFalseState != null && psTrueState != null)
                                    {
                                        //Debug.WriteLine(pssCurrent.ID + "=>" + psFalseState.ID);

                                        //set the next state to be the one that the plan preferred
                                        int spaceIndex = sAction.IndexOf(' ');
                                        if (spaceIndex == -1)
                                            spaceIndex = sAction.IndexOf(Domain.DELIMITER_CHAR);
                                        char lastWord = sAction[spaceIndex - 1];
                                        if (lastWord == 'f')
                                        {
                                            stateStack.Push(psTrueState);
                                            pssCurrent = psFalseState;
                                        }
                                        else
                                        {
                                            stateStack.Push(psFalseState);
                                            pssCurrent = psTrueState;
                                        }
                                    }
                                    else
                                    {
                                        pssCurrent = psTrueState;
                                    }
                                }

                                cActions++;

                                bGoalReached = pssCurrent.IsGoalState();
                                if (bGoalReached)
                                {

                                    pssCurrent.UpdateClosedStates(lClosedStates, alreadyVisitedStates, domain);

                                    lGoalStates.Add(pssCurrent);
                                    pssCurrent = null;
                                    break;
                                }

                                if (SDR_OBS)
                                {
                                    List<Action> lObservationActions = bsInitial.Problem.Domain.GroundAllObservationActions(pssCurrent.Observed, true);
                                    foreach (Action aObserve in lObservationActions)
                                    {
                                        Predicate pObserve = ((PredicateFormula)aObserve.Observe).Predicate;
                                        if (!pssCurrent.Observed.Contains(pObserve) && !pssCurrent.Observed.Contains(pObserve.Negate()))
                                        {
                                            pssCurrent.ApplyOffline(aObserve, out bool bObservationPreconditionFailed, out fObserved, out psTrueState, out psFalseState);
                                            if (psTrueState != null && psFalseState != null)
                                            {
                                                stateStack.Push(psTrueState);
                                                pssCurrent = psFalseState;
                                            }
                                        }
                                    }
                                }

                            }
                        }
                        if (pssCurrent != null)
                            stateStack.Push(pssCurrent);
                    }
                    else
                    {
                        if (!bDone)
                        {
                            if (pssCurrent.IsDeadEndState() == DeadEndExistence.DeadEndTrue)
                                Debug.WriteLine("*");
                            if (pssCurrent.IsGoalState())
                                Debug.WriteLine("*");
                            Debug.WriteLine("No plan was found!!");
                        }
                    }
                }
            }


            DateTime dtEnd = DateTime.Now;
            tsTotal = dtEnd - dtStart;
            HashSet<int> lNodes = new HashSet<int>();
            GetAllNodes(pssInitial.Plan, lNodes);
            Debug.WriteLine(pssInitial.Plan);
            Console.WriteLine(domain.Name + " done planning, time " + (dtEnd - dtStart).TotalSeconds + " , size " + lNodes.Count);
            Console.WriteLine("----------------------------------------------------------------------------------------------");

            /*
            StreamWriter sw;
            if (Translation == Translations.BestCase || Translation == Translations.Conformant)
                if (pssInitial.MinMishapCount == 0)
                    sw = new StreamWriter(sPath + "CPORoutputBestCase.txt");
                else
                    sw = new StreamWriter(sPath + "CPORoutputMishHap" + pssInitial.MinMishapCount + ".txt");

            else
                sw = new StreamWriter(sPath + "CPORoutput.txt");

            sw.Write(pssInitial.Plan.ToString());
            sw.Close();
            */
            List<string> ll = new List<string>();
            List<ConditionalPlanTreeNode> lHistory = new List<ConditionalPlanTreeNode>();
            int cLeaves = 0;
            bValid = CheckPlan(pssInitial, pssInitial.Plan, lHistory, ll, DateTime.Now, new TimeSpan(0, 2, 0), ref cLeaves);
            if (!bValid)
                Debug.Write("*");
            WritePlan(sPath + "/plan.CPOR." + DeadendStrategy + ".dot", pssInitial, pssInitial.Plan);


            iPolicySize = lNodes.Count;

            Debug.WriteLine(domain.Name + " valid = " + bValid);

            //f(pssInitial.Plan, ll);
        }


        public void f(ConditionalPlanTreeNode cp, List<string> ll)
        {
            if (cp.SingleChild != null)
            {
                //ll.Add(cp.Action.Name);
                ll.Add(cp.SingleChild.ID.ToString());
                f(cp.SingleChild, ll);
            }
            else
            {
                if ((cp.TrueObservationChild != null && cp.FalseObservationChild == null) || (cp.TrueObservationChild == null && cp.FalseObservationChild != null))
                {
                    Debug.WriteLine("bug");
                }
                else
                {
                    if ((cp.TrueObservationChild != null && cp.FalseObservationChild != null))
                    {
                        // ll.Add(cp.Action.Name);
                        List<string> x1 = new List<string>(ll);
                        x1.Add(cp.TrueObservationChild.ID.ToString());
                        //x1.Add("True");
                        List<string> x2 = new List<string>(ll);
                        x2.Add(cp.FalseObservationChild.ID.ToString());
                        //x2.Add("False");
                        f(cp.TrueObservationChild, x1);
                        f(cp.FalseObservationChild, x2);
                    }
                }
            }
        }


        public static bool CheckPlan(string sPlanFile, Domain d, Problem p, out int cNodes)
        {
            bool bComputePlanTree = SDRPlanner.ComputeCompletePlanTree;
            SDRPlanner.ComputeCompletePlanTree = true;
            ConditionalPlanTreeNode nRoot = SDRPlanner.ReadPlan(sPlanFile, d);

            if (nRoot == null)
            {
                cNodes = 0;
                return false;
            }

            BeliefState bsInitial = p.GetInitialBelief();
            PartiallySpecifiedState pssInit = bsInitial.GetPartiallySpecifiedState();

            HashSet<int> lNodes = new HashSet<int>();
            GetAllNodes(nRoot, lNodes);
            cNodes = lNodes.Count;
            int cLeaves = 0;
            bool bValid = CheckPlan(pssInit, nRoot, new List<ConditionalPlanTreeNode>(), new List<string>(), DateTime.Now, new TimeSpan(0, 15, 0), ref cLeaves);
            SDRPlanner.ComputeCompletePlanTree = bComputePlanTree;
            return bValid;
        }


        public bool HasConditionalEffectsWithChangedCondition(Formula f, HashSet<Predicate> known, HashSet<Predicate> changed)
        {
            if (f == null || f is PredicateFormula)
                return false;
            CompoundFormula cf = (CompoundFormula)f;
            if (cf.Operator.Equals("when"))
            {
                foreach (GroundedPredicate gp in cf.Operands[0].GetAllPredicates())
                {
                    if (!known.Contains(gp) && changed.Contains(gp))
                        return true;
                }
            }
            foreach (Formula subF in cf.Operands)
            {
                if (HasConditionalEffectsWithChangedCondition(subF, known, changed))
                    return true;
            }
            return false;
        }
        public static bool CheckPlan(PartiallySpecifiedState pssCurrent, ConditionalPlanTreeNode nCurrent, List<ConditionalPlanTreeNode> lHistory, List<string> ll,
            DateTime dtStart, TimeSpan tsMax, ref int cCheckedLeaves)
        {
            if (lHistory.Count % 10 == 0)
            {
                DateTime dtNow = DateTime.Now;
                TimeSpan ts = dtNow - dtStart;
                if (ts > tsMax)
                {
                    Debug.WriteLine("CheckPlan timeout reached");
                    return true;
                }
            }
            if (cCheckedLeaves % 100 == 0)
                Debug.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b Leaves: " + cCheckedLeaves);
            if (lHistory.Contains(nCurrent))//loop detected
                return false;
            if (pssCurrent == null)
            {
                cCheckedLeaves++;
                return false;
            }
            if (pssCurrent.IsGoalState())
            {
                cCheckedLeaves++;
                return true;
            }

            if (nCurrent.DeadEnd)
            {
                cCheckedLeaves++;
                if (pssCurrent.IsDeadEndState() == DeadEndExistence.DeadEndTrue)
                    return true;
                return false;
            }
            if (nCurrent.Action == null) //stopping not at a deadend or goal
            {
                cCheckedLeaves++;
                return false;
            }
            Formula fObserved = null;
            PartiallySpecifiedState psTrueState, psFalseState;

            pssCurrent.ApplyOffline(nCurrent.Action, out bool bPreconditionFailed, out fObserved, out psTrueState, out psFalseState, true);
            if (bPreconditionFailed || (psTrueState == null && psFalseState == null))
            {
                //Debug.WriteLine("BUGBUG");
                return false;
            }

            lHistory.Add(nCurrent);
            if (nCurrent.Action.Observe == null)
            {
                ll.Add(nCurrent.SingleChild.ID.ToString());
                return CheckPlan(psTrueState, nCurrent.SingleChild, lHistory, ll, dtStart, tsMax, ref cCheckedLeaves);
            }
            bool bTrueOk = false;
            bool bFalseOk = false;

            List<string> x1 = new List<string>(ll);
            x1.Add(nCurrent.TrueObservationChild.ID.ToString());

            List<string> x2 = new List<string>(ll);
            x2.Add(nCurrent.FalseObservationChild.ID.ToString());


            List<ConditionalPlanTreeNode> lFalseHistory = new List<ConditionalPlanTreeNode>(lHistory);
            List<ConditionalPlanTreeNode> lTrueHistory = new List<ConditionalPlanTreeNode>(lHistory);


            if (psTrueState == null)
            {
                bTrueOk = true;
            }
            else
            {
                if (nCurrent.TrueObservationChild == null)
                {
                    Debug.WriteLine("BUG");
                    return false;
                }
                bTrueOk = CheckPlan(psTrueState, nCurrent.TrueObservationChild, lTrueHistory, x1, dtStart, tsMax, ref cCheckedLeaves);
            }
            if (psFalseState == null)
            {
                bFalseOk = true;
            }
            else
            {

                if (nCurrent.FalseObservationChild == null)
                {
                    Debug.WriteLine("BUG");
                    return false;
                }
                bFalseOk = CheckPlan(psFalseState, nCurrent.FalseObservationChild, lFalseHistory, x2, dtStart, tsMax, ref cCheckedLeaves);
            }
            if (bTrueOk && bFalseOk)
                return true;
            return false;
        }


        public static ConditionalPlanTreeNode ReadPlan(string sPlanFile, Domain d)
        {
            StreamReader sr = new StreamReader(sPlanFile);
            Dictionary<int, ConditionalPlanTreeNode> dNodes = new Dictionary<int, ConditionalPlanTreeNode>();
            Dictionary<int, bool> dObservationNodes = new Dictionary<int, bool>();
            Dictionary<int, HashSet<int>> dEdges = new Dictionary<int, HashSet<int>>();
            string sLine = sr.ReadLine(); //digraph contingent_plan {
            sLine = sr.ReadLine(); //_nil [style="invis"];
            List<string> lLines = new List<string>();
            while (!sr.EndOfStream)
                lLines.Add(sr.ReadLine().Trim().ToLower());

            for (int i = 0; i < lLines.Count; i++)
            {
                sLine = lLines[i];
                if (sLine.Contains("_nil") || sLine.Contains('}'))
                    continue;
                sLine = sLine.Replace(";", "");
                if (sLine.Contains("->")) //edge
                {
                    sLine = sLine.Replace("->", " ");
                    string[] aLine = sLine.Split(new char[] { ' ' }, StringSplitOptions.RemoveEmptyEntries);
                    int idx1 = int.Parse(aLine[0]);
                    int idx2 = int.Parse(aLine[1]);
                    if (!dEdges.ContainsKey(idx1))
                        dEdges[idx1] = new HashSet<int>();
                    dEdges[idx1].Add(idx2);
                }
                else //node
                {
                    string[] aLine = sLine.Split(new char[] { '[', '\"' });
                    int idx = int.Parse(aLine[0]);
                    string sAction = aLine[2].ToLower();
                    if (sLine.Contains("\"box\""))
                    {
                        if (sAction == "true" || sAction.Contains("detdup_0"))
                            dObservationNodes[idx] = true;
                        else
                            dObservationNodes[idx] = false;
                    }
                    else
                    {
                        ConditionalPlanTreeNode n = new ConditionalPlanTreeNode();
                        if (sAction.Contains("?")) //deadend
                        {
                            n.DeadEnd = true;
                        }
                        else if (sAction.Contains("goal"))
                        {

                        }
                        else
                        {
                            if (sAction.Contains("sensor"))
                            {
                                sAction = sAction.Replace("sensor-", "");
                                sAction = sAction.Replace("__sensor__-obs0", "");
                            }
                            //Action a = d.GroundActionByName(sAction.Split(new char[] { '_', ' ' }));
                            Action a = d.GroundActionByName(sAction.Split(new char[] { ' ' }));
                            if (a == null)
                                throw new Exception("Unknown action: " + sLine);
                            n.Action = a;
                        }
                        n.IndexInPlanFile = idx;
                        dNodes[idx] = n;
                    }
                }
            }
            foreach (KeyValuePair<int, HashSet<int>> p in dEdges)
            {
                if (dNodes.ContainsKey(p.Key))
                {
                    ConditionalPlanTreeNode n = dNodes[p.Key];
                    if (p.Value.Count == 1)
                    {
                        dNodes[p.Key].SingleChild = dNodes[p.Value.First()];
                    }
                    if (p.Value.Count == 2)
                    {
                        foreach (int i in p.Value)
                        {
                            int iChild = dEdges[i].First();
                            if (dObservationNodes[i])
                            {
                                dNodes[p.Key].TrueObservationChild = dNodes[iChild];
                            }
                            else
                            {
                                dNodes[p.Key].FalseObservationChild = dNodes[iChild];
                            }
                        }
                    }
                }
            }
            if (dNodes.Count > 0)
                return dNodes[0];
            return null;
        }


        public void WritePlan(string sPlanFile, PartiallySpecifiedState pssInitial, ConditionalPlanTreeNode nInitial)
        {
            StreamWriter sw = new StreamWriter(sPlanFile);
            Dictionary<ConditionalPlanTreeNode, int> dNodes = new Dictionary<ConditionalPlanTreeNode, int>();
            Dictionary<int, bool> dObservationNodes = new Dictionary<int, bool>();
            List<string> lEdges = new List<string>();
            dNodes[nInitial] = 0;
            CollectGraph(pssInitial, nInitial, dNodes, dObservationNodes, lEdges);

            sw.WriteLine("digraph contingent_plan {");
            sw.WriteLine("\t_nil [style=\"invis\"];");

            foreach (ConditionalPlanTreeNode n in dNodes.Keys)
            {
                if (n.DeadEnd)
                    sw.WriteLine("\t" + dNodes[n] + " [label=\"" + n.ID + ") Deadend\"];");
                else if (n.Action == null) //Goal
                    sw.WriteLine("\t" + dNodes[n] + " [label=\"" + n.ID + ") Goal\"];");
                else
                    sw.WriteLine("\t" + dNodes[n] + " [label=\"" + n.ID + ")" + n.Action.Name + "\"];");
            }
            foreach (var p in dObservationNodes)
            {
                sw.WriteLine("\t" + p.Key + " [label=\"" + p.Value + "\" ,shape=\"box\"];");
            }

            foreach (string s in lEdges)
            {
                sw.WriteLine("\t" + s);
            }
            sw.WriteLine("\t_nil -> 0 [label=\"\"];");
            sw.WriteLine("}");


            sw.Close();
        }

        public void CollectGraph(PartiallySpecifiedState pssCurrent, ConditionalPlanTreeNode nCurrent,
            Dictionary<ConditionalPlanTreeNode, int> dNodes, Dictionary<int, bool> dObservationNodes, List<string> lEdges)
        {
            if (pssCurrent == null)
                return;
            if (pssCurrent.IsGoalState())
                return;

            if (pssCurrent.IsDeadEndState() == DeadEndExistence.DeadEndTrue)
                return;
            if (nCurrent.DeadEnd)
                return;
            if (nCurrent.Action == null)
                return;
            Formula fObserved = null;
            PartiallySpecifiedState psTrueState, psFalseState;


            int cNodes = dNodes.Count + dObservationNodes.Count;

            pssCurrent.ApplyOffline(nCurrent.Action, out bool bPreconditionFailed, out fObserved, out psTrueState, out psFalseState);
            if (bPreconditionFailed || psTrueState == null)
            {
                Debug.WriteLine("BUG");
                return;
            }

            if (nCurrent.Action.Observe == null)
            {
                if (!dNodes.ContainsKey(nCurrent.SingleChild))
                {
                    dNodes.Add(nCurrent.SingleChild, cNodes);
                    CollectGraph(psTrueState, nCurrent.SingleChild, dNodes, dObservationNodes, lEdges);
                }
                lEdges.Add(dNodes[nCurrent] + " -> " + dNodes[nCurrent.SingleChild] + ";");

            }
            else
            {
                int iFalseObservation = cNodes;
                dObservationNodes[cNodes] = false;
                cNodes++;
                int iTrueObservation = cNodes;
                dObservationNodes[cNodes] = true;
                cNodes++;

                bool bTrueExists = dNodes.ContainsKey(nCurrent.TrueObservationChild);
                bool bFalseExists = dNodes.ContainsKey(nCurrent.FalseObservationChild);
                if (!bTrueExists)
                {
                    dNodes[nCurrent.TrueObservationChild] = cNodes;
                    cNodes++;
                }
                if (!bFalseExists)
                {
                    dNodes[nCurrent.FalseObservationChild] = cNodes;
                    cNodes++;
                }

                lEdges.Add(dNodes[nCurrent] + " -> " + iFalseObservation + ";");
                lEdges.Add(iFalseObservation + " -> " + dNodes[nCurrent.FalseObservationChild] + ";");

                lEdges.Add(dNodes[nCurrent] + " -> " + iTrueObservation + ";");
                lEdges.Add(iTrueObservation + " -> " + dNodes[nCurrent.TrueObservationChild] + ";");


                if (psTrueState != null)
                {
                    if (nCurrent.TrueObservationChild == null)
                    {
                        Debug.WriteLine("BUGBUG");
                        return;
                    }
                    if (!bTrueExists)
                    {

                        CollectGraph(psTrueState, nCurrent.TrueObservationChild, dNodes, dObservationNodes, lEdges);
                    }
                }
                if (psFalseState != null)
                {

                    if (nCurrent.FalseObservationChild == null)
                    {
                        Debug.WriteLine("BUGBUG");
                        return;
                    }
                    CollectGraph(psFalseState, nCurrent.FalseObservationChild, dNodes, dObservationNodes, lEdges);
                }
            }
        }


        public static void GetAllNodes(ConditionalPlanTreeNode nCurrent, HashSet<int> lVisited)
        {
            if (!lVisited.Contains(nCurrent.ID))
            {
                lVisited.Add(nCurrent.ID);
                if (nCurrent.SingleChild != null)
                {
                    GetAllNodes(nCurrent.SingleChild, lVisited);
                }
                else if (nCurrent.TrueObservationChild != null && nCurrent.FalseObservationChild != null)
                {
                    GetAllNodes(nCurrent.TrueObservationChild, lVisited);
                    GetAllNodes(nCurrent.FalseObservationChild, lVisited);
                }
            }
        }

        public static int PlanSize(ConditionalPlanTreeNode nCurrent, Dictionary<int, int> d, HashSet<int> lVisited)
        {
            if (d.ContainsKey(nCurrent.ID))
                return nCurrent.ID;
            if (lVisited.Contains(nCurrent.ID))
                return 0;
            lVisited.Add(nCurrent.ID);
            if (nCurrent.SingleChild != null)
            {
                int size = PlanSize(nCurrent.SingleChild, d, lVisited) + 1;
                d[nCurrent.ID] = size;
                return size;
            }
            else if (nCurrent.TrueObservationChild != null && nCurrent.FalseObservationChild != null)
            {
                int size1 = PlanSize(nCurrent.TrueObservationChild, d, lVisited);
                int size2 = PlanSize(nCurrent.FalseObservationChild, d, lVisited);
                d[nCurrent.ID] = size1 + size2 + 1;
                return size1 + size2 + 1;
            }
            return 1;
        }


        /*private List<Action> GetExistingPlan(PartiallySpecifiedState pssCurrent, Dictionary<GroundedPredicate, Dictionary<PartiallySpecifiedState, List<Action>>> dFinalPlans, Domain d)
        {
            GroundedPredicate gpAt = null;
            foreach (GroundedPredicate gp in pssCurrent.Observed)
                if (gp.Name == "at" && gp.Negation == false)
                    gpAt = gp;
            if (!dFinalPlans.ContainsKey(gpAt))
                return null;
            Dictionary<PartiallySpecifiedState, List<Action>> dSamePosition = dFinalPlans[gpAt];
            foreach (KeyValuePair<PartiallySpecifiedState, List<Action>> pair in dSamePosition)
            {
                if (pssCurrent.ToString() == "(at p3-5)")
                    Debug.WriteLine("*");
                bool bKnownContained = pair.Key.m_lOfflinePredicatesKnown == null || pair.Key.m_lOfflinePredicatesKnown.Count == 0 || pair.Key.m_lOfflinePredicatesKnown.IsSubsetOf(pssCurrent.Observed);
                bool bUnknownContained = pair.Key.m_lOfflinePredicatesUnknown == null || pair.Key.m_lOfflinePredicatesUnknown.Count == 0 || pair.Key.m_lOfflinePredicatesUnknown.IsSubsetOf(pssCurrent.Hidden);

                if (bKnownContained && bUnknownContained)
                {
                    dFinalPlans[gpAt].Add(pssCurrent, new List<Action>());
                    return dFinalPlans[gpAt][pssCurrent];
                }
                if (CompareRelevantVariables(pair.Key, pssCurrent, pair.Value, d))
                {
                    return pair.Value;
                }

            }
            return null;
        }*/

        HashSet<PartiallySpecifiedState> lFail = new HashSet<PartiallySpecifiedState>();

        private bool CompareRelevantVariables(PartiallySpecifiedState pssSource, PartiallySpecifiedState pssTarget, List<Action> lPlan, Domain d)
        {
            HashSet<Predicate> hsKnownPredicates = new HashSet<Predicate>();

            foreach (GroundedPredicate gpKnown in pssSource.Observed)
            {
                if (d.AlwaysKnown(gpKnown))
                {
                    if (!pssTarget.Observed.Contains(gpKnown))
                        return false;
                    else hsKnownPredicates.Add(gpKnown);
                }
            }
            foreach (Action a in lPlan)
            {
                HashSet<Predicate> lPreconditions = a.Preconditions.GetAllPredicates();
                foreach (Predicate p in lPreconditions)
                {
                    if (!d.AlwaysKnown(p))
                    {
                        if (!pssTarget.Observed.Contains(p))
                            return false;
                        else hsKnownPredicates.Add(p);
                    }
                }
            }
            /*if (pssSource.Predecessor.m_lOfflinePredicatesKnown != null)
            {
                foreach (Predicate p in hsKnownPredicates)
                {
                    Predicate pNegate = p.Negate();
                    if (pssSource.Predecessor.m_lOfflinePredicatesKnown.Contains(pNegate))
                    {
                        if (p.Negation) pssSource.Predecessor.m_lOfflinePredicatesUnknown.Add(pNegate);
                        else pssSource.Predecessor.m_lOfflinePredicatesUnknown.Add(p);
                        //pssSource.Predecessor.m_lOfflinePredicatesKnown.Remove();
                    }
                }
            }
            else pssSource.Predecessor.m_lOfflinePredicatesKnown = hsKnownPredicates;*/
            return true;
        }


        static int c1 = 0;

        public void OnlineReplanning(string sPath, string deadEndFile, Domain domain, Problem problem, bool bSampleDeadendState,
            out int cActions, out int cPlanning, out int cObservations, out TimeSpan tsTime,
            out bool bIntialDeadendState, out bool bFinalStateDeadend, out bool bValid)
        {
            Console.WriteLine("Started online replanning for " + domain.Name + ", " + DateTime.Now);


            //RandomGenerator.Init(iSeed++);
            BeliefState bsInitial = problem.GetInitialBelief();//, bsCurrent = bsInitial, bsNext = null;
            bsInitial.UnderlyingEnvironmentState = null;
            State s = null;

            if (problem.deadEndList.Count == 0)
                bSampleDeadendState = false;

            s = bsInitial.ChooseState(true, bSampleDeadendState);
            c1++;

            bIntialDeadendState = false;
            bFinalStateDeadend = false;

            foreach (Formula f in problem.deadEndList)
            {
                if (f.IsTrue(s.Predicates, false))
                    bIntialDeadendState = true;
            }

            if (bSampleDeadendState != bIntialDeadendState)
                Debug.Write("*");

            bool bPreconditionFailure = false;

            PartiallySpecifiedState pssCurrent = bsInitial.GetPartiallySpecifiedState(), pssNext = null;
            List<State> lTrueStates = new List<State>();
            lTrueStates.Add(pssCurrent.UnderlyingEnvironmentState);
            List<string> lActions = new List<string>();

            List<List<string>> lExecutedPlans = new List<List<string>>();
            List<State> lChosen = new List<State>();

            /*
            List<State> lStates = new List<State>();
            Process proc = Process.GetCurrentProcess();
            for (int i = 0; i < 1000; i++)
            {
                Debug.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" + i + ", " + (proc.WorkingSet64 / 1000000));
                lStates.Add(bsInitial.ChooseState(true));
            }
            */

            Formula fObserved = null;
            cActions = 0;
            cPlanning = 0;
            cObservations = 0;

            bool bPlanEndedSuccessfully = false, bGoalReached = false, bDeadEndReached = false;
            DateTime dtStart = DateTime.Now;
            while (!bGoalReached && !bDeadEndReached)
            {
                State sChosen = null;


                if (cActions >= 100000)
                    break;
                //used only for finding loops
                if (lExecutedPlans.Count > 20)
                {
                    if (pssCurrent.Equals(pssCurrent.Predecessor.Predecessor))
                    {
                        if (pssCurrent.Predecessor.Equals(pssCurrent.Predecessor.Predecessor.Predecessor))
                        {
                            if (SameList(lExecutedPlans[lExecutedPlans.Count - 1], lExecutedPlans[lExecutedPlans.Count - 3]))
                            {
                                if (SameList(lExecutedPlans[lExecutedPlans.Count - 2], lExecutedPlans[lExecutedPlans.Count - 4]))
                                {
                                    //throw new Exception("stuck in a loop");
                                    //Debug.WriteLine("Stuck in a loop");
                                }
                            }
                        }
                    }
                    bool bAllEmpty = true;
                    for (int i = 1; i <= 4; i++)
                        if (lExecutedPlans[lExecutedPlans.Count - i].Count != 0)
                            bAllEmpty = false;
                    if (bAllEmpty)
                        throw new Exception("stuck in a loop");
                }
                List<Action> cPlan = null;
                //List<string> lPlan = MineSweeperPlan(pssCurrent, domain);

                List<string> lPlan = null;
                if (GivenPlanFile != null)
                    lPlan = ReadPlanSimple(GivenPlanFile);
                else
                {
                    if (UseDomainSpecificHeuristics)
                    {
                        if (domain.Name.Contains("LargeWumpus"))
                            lPlan = LargeWumpusDomain.LargeWumpusHeuristic(pssCurrent, domain);
                        else if (domain.Name.Contains("Battleship"))
                            lPlan = Battleship.BattleshipHeuristic(pssCurrent, domain, fObserved);
                        else if (domain.Name.Contains("MineSweeper"))
                            lPlan = MineSweeper.MineSweeperHeuristic(pssCurrent, domain, fObserved);
                        else if (domain.Name.Contains("sliding-doors"))
                            lPlan = ChooseLocalizeAction(pssCurrent, domain);
                        else if (domain.Name.Contains("RockSample"))
                            lPlan = RockSample.RockSampleHeuristic(pssCurrent, domain);
                        else if (domain.Name.Contains("MasterMind"))
                            lPlan = MasterMind.MasterMindHeuristic(pssCurrent, domain);
                        else
                            lPlan = Plan(sPath, pssCurrent, out sChosen, ref cPlan);
                    }
                    else
                    {

                        List<Formula> lDeadends = null;
                        DeadEndExistence isDeadEnd = pssCurrent.IsDeadEndExistenceAll(out lDeadends);
                        if (isDeadEnd == DeadEndExistence.DeadEndTrue)
                        {
                            //Debug.WriteLine("dead end state is");
                            //Debug.WriteLine(daedend);
                            bDeadEndReached = true;
                            break;

                        }
                        if (isDeadEnd == DeadEndExistence.MaybeDeadEnd)
                        // || daedend.Size == 2
                        {
                            lPlan = PlanToObserveDeadEnd(sPath, deadEndFile, pssCurrent, lDeadends, bPreconditionFailure, out sChosen, ref cPlan);
                        }


                        if (lPlan == null)
                        {
                            lPlan = Plan(sPath, pssCurrent, out sChosen, ref cPlan);
                        }

                        if (lPlan == null)
                            throw new Exception("Could not plan for the current state");


                    }
                }
                cPlanning++;
                lChosen.Add(sChosen);
                bPlanEndedSuccessfully = true;

                lExecutedPlans.Add(new List<string>());

                if (lPlan != null)
                {
                    foreach (string sAction in lPlan)
                    {

                        if (!IsReasoningAction(sAction.ToLower()))
                        {
                            Debug.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" +
                                domain.Name + ": " + cActions + "/" + lPlan.Count + ", memory:" + Process.GetCurrentProcess().PrivateMemorySize64 / 1000000 + "MB        ");
                            //domain.Name + ": " + cActions + "/" + lPlan.Count + ", predicates:" + Predicate.PredicateCount + ", formulas:" + Formula.FormulaCount + ", observed: " + pssCurrent.Observed.Count() + "   ");
                            Debug.WriteLine("");
                            TimeSpan ts = DateTime.Now - dtStart;
                            if (ts.TotalMinutes > 60)
                                throw new Exception("Execution taking too long");
                            Debug.WriteLine((int)(ts.TotalMinutes) + "," + cActions + ") " + domain.Name + ", executing action " + sAction);

                            lExecutedPlans.Last().Add(sAction);
                            DateTime dtBefore = DateTime.Now;
                            //bsNext = bsCurrent.Apply(sAction, out fObserved);
                            //if (sAction == "move p6-4 p6-5")
                            //    Debug.WriteLine("*");
                            pssNext = pssCurrent.Apply(sAction, out fObserved);

                            List<Formula> lDeadends = null;
                            if (pssNext != null)
                            {
                                bPreconditionFailure = false;
                                DeadEndExistence isDeadEnd = pssNext.IsDeadEndExistenceAll(out lDeadends);
                                if (isDeadEnd == DeadEndExistence.DeadEndTrue)
                                {
                                    pssCurrent = pssNext;
                                    bDeadEndReached = true;
                                    bPlanEndedSuccessfully = true;
                                    break;

                                }
                            }
                            Debug.WriteLine("Apply time: " + (DateTime.Now - dtBefore).TotalSeconds);
                            if (pssNext == null /*&& !sAction.ToLower().Contains("-kw")*/)
                            {
                                bPlanEndedSuccessfully = false;
                                Debug.WriteLine(domain.Name + ", cannot execute " + sAction);

                                if (domain.Name.Contains("RockSample"))
                                {
                                    //cActions = 1000;
                                }
                                bPreconditionFailure = true;
                                break;
                            }
                            else
                            {
                                lTrueStates.Add(pssNext.UnderlyingEnvironmentState);

                                if (pssNext != null)
                                {
                                    lActions.Add(sAction);

                                    if (SDR_OBS)
                                    {
                                        List<Action> lObservationActions = bsInitial.Problem.Domain.GroundAllObservationActions(pssNext.Observed, true);
                                        foreach (Action a in lObservationActions)
                                        {
                                            Predicate pObserve = ((PredicateFormula)a.Observe).Predicate;
                                            if (!pssNext.Observed.Contains(pObserve) && !pssNext.Observed.Contains(pObserve.Negate()))
                                            {
                                                pssNext = pssNext.Apply(a, out fObserved);
                                                lActions.Add(a.Name);
                                                cObservations++;
                                                Debug.WriteLine(domain.Name + ", observed " + fObserved);
                                                cActions++;
                                            }
                                        }
                                    }
                                    cActions++;
                                    pssCurrent = pssNext;
                                    if (fObserved != null)
                                    {
                                        cObservations++;
                                        Debug.WriteLine(domain.Name + ", observed " + fObserved);

                                        //bPlanEndedSuccessfully = false;
                                        //break;
                                        /*
                                        if (!WriteAllKVariations)
                                        {
                                            bPlanEndedSuccessfully = false;
                                            break;
                                        }
                                         * */
                                    }
                                }
                                else
                                {
                                    //Debug.WriteLine("Skipping inapplicable KW action...");
                                }
                            }
                        }
                    }
                }

                if (bDeadEndReached)
                {
                    DateTime dtBefore = DateTime.Now;
                    Debug.WriteLine("Dead End time: " + (DateTime.Now - dtBefore).TotalSeconds);
                    bFinalStateDeadend = true;
                }
                if (bPlanEndedSuccessfully)
                {
                    DateTime dtBefore = DateTime.Now;
                    bGoalReached = pssCurrent.IsGoalState();
                    Debug.WriteLine("Goal time: " + (DateTime.Now - dtBefore).TotalSeconds);
                }
                else
                {
                    GroundedPredicate gpDead = new GroundedPredicate("dead");
                    if (pssCurrent.Observed.Contains(gpDead))
                        bGoalReached = true;
                    if (domain.Name.Contains("mines-"))
                        break;
                }
            }
            bValid = pssCurrent.IsGoalState();
            if (!bValid)
                bValid = pssCurrent.IsDeadEndState() == DeadEndExistence.DeadEndTrue;


            tsTime = DateTime.Now - dtStart;

            int cHistory = 0;
            PartiallySpecifiedState pssIt = pssCurrent;
            while (pssIt != null)
            {
                pssIt = pssIt.Predecessor;
                cHistory++;
            }
            cActions = cHistory;
            Console.WriteLine("Actions: " + cHistory);
            Console.WriteLine("Average time - " + tsTime.TotalSeconds * 1.0 / cActions);
            Console.WriteLine("Total time - " + tsTime.TotalSeconds);
            Console.WriteLine("*******************************************************************************");
        }


        private List<string> ChooseRandomAction(PartiallySpecifiedState pssCurrent, Domain d)
        {
            List<Action> lActions = d.GroundAllActions(pssCurrent.Observed, true);
            List<Action> lEffectsActions = new List<Action>();
            List<string> lPlan = new List<string>();
            int iOpen = -1;
            foreach (Action a in lActions)
            {
                if (a.Observe != null && a.Effects == null)//pure observation actions go first
                    lPlan.Add(a.Name.Replace("_", " "));
                else
                    lEffectsActions.Add(a);
                if (a.Name.StartsWith("open"))
                    iOpen = lEffectsActions.Count - 1;
            }
            if (iOpen >= 0)
            {
                lPlan.Add(lEffectsActions[iOpen].Name.Replace("_", " "));
            }
            else
            {
                int iRnd = RandomGenerator.Next(lEffectsActions.Count);
                lPlan.Add(lEffectsActions[iRnd].Name.Replace("_", " "));
            }
            return lPlan;
        }

        static int iStep = 0;
        private List<string> MineSweeperPlan(PartiallySpecifiedState pssCurrent, Domain d)
        {
            List<string> lPlan = new List<string>();

            if (iStep == 0)
            {
                lPlan.Add("open-cell-at-step" + iStep);
                iStep++;
            }
            else
            {
                foreach (GroundedPredicate gp in pssCurrent.Observed)
                {
                    if (gp.Name == "need-gather-obs0-at" && gp.Negation == false)
                    {
                        Constant c = gp.Constants[0];
                        for (int i = 0; i < 9; i++)
                        {
                            lPlan.Add("gather-obs" + i + " " + c.Name);
                            lPlan.Add("advance-gather-counter" + i + " " + c.Name);
                        }
                        lPlan.Add("advance-step");

                        int[] aFlagSteps = new int[] { 5, 6, 7, 9 };
                        while (aFlagSteps.Contains(iStep))
                        {
                            lPlan.Add("put-flag-at-step" + iStep);
                            lPlan.Add("advance-step");
                            iStep++;
                        }

                        lPlan.Add("open-cell-at-step" + iStep);
                        iStep++;
                    }

                }
            }
            return lPlan;
        }

        bool bFirstLocalize = true;

        private List<string> ChooseLocalizeAction(PartiallySpecifiedState pssCurrent, Domain d)
        {
            List<string> lPlan = new List<string>();
            if (bFirstLocalize)
                bFirstLocalize = false;
            else
            {
                bool bValidUp = pssCurrent.Observed.Contains(new GroundedPredicate("free-up"));
                bool bValidRight = pssCurrent.Observed.Contains(new GroundedPredicate("free-right"));
                bool bValidDown = pssCurrent.Observed.Contains(new GroundedPredicate("free-down"));
                bool bValidLeft = pssCurrent.Observed.Contains(new GroundedPredicate("free-left"));
                /*
                List<string> lMoveActions = new List<string>();
                if (bValidDown)
                    lMoveActions.Add("move-down");
                if (bValidUp)
                    lMoveActions.Add("move-up");
                if (bValidLeft)
                    lMoveActions.Add("move-left");
                if (bValidRight)
                    lMoveActions.Add("move-right");
                Random rnd = new Random();
                int idx = rnd.Next(lMoveActions.Count);
                lPlan.Add(lMoveActions[idx]);
                 */
                if (bValidUp)
                    lPlan.Add("move-up");
                else if (bValidRight)
                    lPlan.Add("move-right");

            }

            lPlan.Add("checking");
            lPlan.Add("sense-left");
            lPlan.Add("sense-right");
            lPlan.Add("sense-up");
            lPlan.Add("sense-down");


            return lPlan;
        }

        private bool SameList(List<string> l1, List<string> l2)
        {
            if (l1 == null && l2 == null)
                return true;
            if (l1 == null && l2 != null)
                return false;
            if (l1 != null && l2 == null)
                return false;

            if (l1.Count != l2.Count)
                return false;
            for (int i = 0; i < l1.Count; i++)
                if (l1[i] != l2[i])
                    return false;
            return true;
        }

        private bool IsReasoningAction(string sAction)
        {
            if (sAction.StartsWith("merge") || sAction.StartsWith("refute") || sAction.StartsWith("unmerge") || sAction.StartsWith("tagmerge"))
                return true;
            if (sAction.Contains("knowledgegain") || sAction.Contains("knowledgeloss"))
                return true;
            if (sAction.Contains("advanceoptions"))
                return true;
            if (!sAction.StartsWith("r"))
                return false;
            for (int i = 1; i < sAction.Length; i++)
                if (sAction[i] < '0' || sAction[i] > '9')
                    return false;
            return true;
        }

        static int RandomSeed = 18;

        public void Start()
        {
            int cActions = 0, cPlanning = 0, cObservations = 0;
            bool bInitialStateDeadend = false, bFinalStateDeadend = false, bValid = false;
            TimeSpan tsTime = new TimeSpan(0);
#if !DEBUG

            try
#endif
            {
                Stopwatch sw = new Stopwatch();
                sw.Start();
                //OnlineReplanning(Data.Path, Data.DeadEndFile, Data.Domain, Data.Problem, out cActions, out cPlanning, out cObservations, out tsTime);

                RandomGenerator.Init(RandomSeed++);

                if (SDRPlanner.Planner == Planners.FF_WSL || SDRPlanner.Planner == Planners.TRAPPER_WSL)
                {
                    File.Copy(Program.BASE_PATH + "/Planners/ff_wsl", Data.Path + "/ff_wsl", true);
                    File.Copy(Program.BASE_PATH + "/Planners/trapper_wsl", Data.Path + "/trapper_wsl", true);
                }

                //SDR_OBS = true;
                //OnlineReplanningII(Data.Path, Data.DeadEndFile, Data.Domain, Data.Problem, out cActions, out cPlanning, out cObservations, out tsTime);

                //try
                {
                    if (!ComputeCompletePlanTree)
                        OnlineReplanning(Data.Path, Data.DeadEndFile, Data.Domain, Data.Problem, Data.SampleDeadendState,
                            out cActions, out cPlanning, out cObservations,
                            out tsTime, out bInitialStateDeadend, out bFinalStateDeadend, out bValid);
                    else
                        OfflinePlanning(Data.Path, Data.DeadEndFile, Data.Domain, Data.Problem, out tsTime, out cPlanning, out cActions, out bValid);
                }
                //catch(Exception e)
                {
                    //Debug.WriteLine(e);
                    //Data.Exception = e.ToString();
                }
                sw.Stop();
                Debug.WriteLine("Planning time: " + sw.Elapsed);

                if (!bValid)
                {
                    Data.Exception = "Invalid plan";
                }
                Data.Actions = cActions;
                Data.Planning = cPlanning;
                Data.Time = tsTime;
                Data.Observations = cObservations;
                Data.InitialStateDeadend = bInitialStateDeadend;
                Data.FinalStateDeadend = bFinalStateDeadend;
            }
#if !DEBUG
            catch (Exception e)
            {
                 Data.Exception = e.ToString();
                Console.Error.WriteLine(e);
                Console.Error.WriteLine("FAILED: " + Data.Domain.Name + ", " + Data.Problem.Name);
            }
#endif
        }

        public void TerminateFFPRocesses(Thread t)
        {
            if (FFProcesses.ContainsKey(t))
            {
                if (FFProcesses[t] != null)
                {
                    if (!FFProcesses[t].HasExited)
                    {
                        FFProcesses[t].Kill();
                        FFProcesses[t].WaitForExit();
                    }
                }
                FFProcesses.Remove(t);
            }
        }

        public class ExecutionData
        {
            public bool FinalStateDeadend { get; set; }
            public bool InitialStateDeadend { get; set; }

            public int Observations { get; set; }
            public int Actions { get; set; }
            public int Planning { get; set; }
            public TimeSpan Time { get; set; }
            public Domain Domain { get; set; }
            public Problem Problem { get; set; }

            public bool SampleDeadendState { get; set; }
            public string Path { get; set; }
            public string DeadEndFile { get; set; }
            public string Exception { get; set; }
            public bool Failure { get { return Exception != ""; } }

            public DeadendStrategy DeadendStrategy { get; set; }

            public ExecutionData(string sPath, string sDeadEndFile, Domain d, Problem p, DeadendStrategy ds)
            {
                Domain = d;
                Problem = p;
                Path = sPath;
                DeadEndFile = sDeadEndFile;
                Exception = "";
                DeadendStrategy = ds;
                SampleDeadendState = false;
            }
        }
    }
}
