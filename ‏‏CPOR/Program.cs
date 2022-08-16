using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Threading;

namespace CPOR
{
    class Program
    {
        // public static string BASE_PATH = @"D:\research\projects\PDDL";
        //Guy path
        //  public static string BASE_PATH = @"D:\Dropbox\SDR\Deadends";
        //lera path
        public static string BASE_PATH = @"C:/Users/shanigu/OneDrive - Ben Gurion University of the Negev/Research/projects/SDR.1/DeadEnds/";
        //public static string BASE_PATH = @"C:/Deadends/";
        //C:\Users\lera\Dropbox\SDR\

        public static string Path;


        public static string ResultsFile = "Results.txt";
#if DEBUG
        public static bool RedirectShellOutput = false;
#else
        public static bool RedirectShellOutput = true;
#endif
        public static int MaxTimePerProblem = 15;//minutes
        public static bool UseCLG = false;

        public static Mutex m_mCLGMutex = new Mutex();
        public static string deadEndPath = @"D:\Dropbox\SDR\Deadends\Domains\sokoban\‏‏‏‏‏‏‏‏prob11Dead.pddl";
        //public static string deadEndPath = @"C:\Users\lera\Desktop\DeadEnds\Domains\sokoban\‏‏‏‏‏‏‏‏prob11Dead.pddl";

        static bool GetCleanName(string sFile, out string sCleanFileName)
        {
            sCleanFileName = "";
            bool bFound = false;
            for (int i = 0; i < sFile.Length; i++)
            {
                int c = (int)sFile[i];
                if (c < 256)
                    sCleanFileName += sFile[i];
                else
                    bFound = true;
            }
            return bFound;
        }

        static void RemoveStrangeChars(string sPath)
        {
            DirectoryInfo dir = new DirectoryInfo(sPath);
            foreach (DirectoryInfo dSub in dir.GetDirectories())
            {
                string sClean = "";
                if (GetCleanName(dSub.Name, out sClean))
                {
                    Debug.WriteLine("Moving dir " + dSub.Name + " to  " + sClean);
                    dSub.MoveTo(dir.FullName + "/" + sClean);
                }
            }
            foreach (DirectoryInfo dSub in dir.GetDirectories())
            {
                RemoveStrangeChars(dSub.FullName);
            }
            string[] aFiles = Directory.GetFiles(sPath);
            foreach (string sFile in aFiles)
            {
                if (GetCleanName(sFile, out string sCleanFileName))
                {
                    Debug.WriteLine("Moving " + sFile + " to  " + sCleanFileName);
                    File.Move(sFile, sCleanFileName);
                }
            }
        }

        static void TestKReplanner(string sBenchmarkPath, int cAttempts, bool offline)
        {

            RandomGenerator.Init();
            string sExePath = BASE_PATH + @"\PDDL\KReplanner\";

            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sBenchmarkPath + "d.pddl");
            Problem problem = parser.ParseProblem(sBenchmarkPath + "p.pddl", deadEndPath, domain);

            BeliefState bsInitial = problem.GetInitialBelief();

            string sOutput = "";

            DirectoryInfo di = new DirectoryInfo(sBenchmarkPath);
            foreach (FileInfo fi in di.GetFiles())
            {
                if (fi.Name.Contains("k_replanner"))
                    fi.Delete();
            }

            sOutput = problem.Name + "\t" + DateTime.Now;
            DateTime dtBeforeTranslate = DateTime.Now;

            domain.WriteKReplannerDomain(sBenchmarkPath + "d.k_replanner.pddl");

            sOutput += "\t" + (DateTime.Now - dtBeforeTranslate).TotalSeconds;


            int cFailures = 0;
            List<double> lActions = new List<double>();
            List<double> lTimes = new List<double>();

            Debug.WriteLine("Done " + problem.Name + " translation");

            for (int i = 1; i <= cAttempts; i++)
            {
                DateTime dtStart = DateTime.Now;
                Debug.WriteLine("++++++++++++++++++++++++++++++++++++++++++++++++++++");
                State sChosen = null;
                Process pKReplanner = new Process();
                pKReplanner.StartInfo.WorkingDirectory = sExePath;
                pKReplanner.StartInfo.FileName = sExePath + "k_replanner.exe";
                pKReplanner.StartInfo.UseShellExecute = false;

                string sProblemName = "p." + i + ".k_replanner.pddl";
                sChosen = problem.WriteKReplannerProblem(sBenchmarkPath + sProblemName, bsInitial);

                pKReplanner.StartInfo.Arguments = //"--no-remove-intermediate-files " + 
                    sBenchmarkPath + "d.k_replanner.pddl " + sBenchmarkPath + sProblemName;

                Debug.WriteLine("Starting KReplanner");
                File.Delete(sBenchmarkPath + "KReplanner.plan.txt");
                if (RedirectShellOutput)
                {
                    pKReplanner.StartInfo.RedirectStandardOutput = true;
                    pKReplanner.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);
                }
                pKReplanner.Start();
                if (RedirectShellOutput)
                {
                    //string sOutput = p.StandardOutput.ReadToEnd();
                    pKReplanner.BeginOutputReadLine();
                }                 /*
                    StreamWriter swOutput = new StreamWriter(sBenchmarkPath + "CLGOutput.txt");
                    swOutput.Write(pCLG.StandardOutput.ReadToEnd());
                    swOutput.Close();                
                 * */
                if (!pKReplanner.WaitForExit(1000 * 60 * 30))//30 minutes max
                {
                    pKReplanner.Kill();
                    cFailures++;
                }
                else if (!File.Exists(sBenchmarkPath + sProblemName + ".plan"))
                {
                    cFailures++;
                }
                else
                {
                    StreamReader sr = new StreamReader(sBenchmarkPath + sProblemName + ".plan");
                    List<string> lPlan = new List<string>();
                    while (!sr.EndOfStream)
                    {
                        string sLine = sr.ReadLine();
                        /*
                        string sParsedLine = sLine.Trim().ToLower().Replace("_", " ").
                            Replace("smell wumpus", "smell_wumpus").Replace("cd ", "cd_").Replace("my file", "my_file")
                            .Replace(" package ", "_package_").Replace(" truck ", "_truck_")
                            //.Replace(" airplane", "_airplane")
                            ;
                        */
                        string sParsedLine = sLine.Trim().Replace("(", "").Replace(")", "");
                        lPlan.Add(sParsedLine);
                    }
                    sr.Close();
                    int cActions = 0;
                    TimeSpan tsTime;
                    DateTime dtBeforeVerification = DateTime.Now;
                    bool bSuccess = true;
                    bSuccess = TestCLGPlan(sBenchmarkPath, domain, problem, lPlan, sChosen, out cActions, out tsTime, offline);
                    if (!bSuccess)
                    {
                        cFailures++;
                        Debug.WriteLine("KReplanner Failed");
                    }
                    else
                    {
                        lActions.Add(cActions);
                        tsTime = dtBeforeVerification - dtStart;
                        lTimes.Add(tsTime.TotalSeconds);
                    }
                }
                Debug.WriteLine("Done " + problem.Name + " execution " + i + "/" + cAttempts);
            }

            m_mCLGMutex.WaitOne();
            StreamWriter sw1 = new StreamWriter(sBenchmarkPath + @"..\KReplannerResults.txt", true);
            sw1.Write(sOutput);
            sw1.Close();
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\KReplannerResults.txt", lActions);
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\KReplannerResults.txt", lTimes);
            sw1 = new StreamWriter(sBenchmarkPath + @"..\KReplannerResults.txt", true);
            sw1.WriteLine("\t" + cFailures);
            sw1.Close();
            m_mCLGMutex.ReleaseMutex();
            Debug.WriteLine("Done " + problem.Name);
        }


        static void TestCLG(string sBenchmarkPath, int cAttempts, bool offline)
        {

            RandomGenerator.Init();
            string sExePath = BASE_PATH + @"\PDDL\CLG\";

            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sBenchmarkPath + "d.pddl");
            Problem problem = parser.ParseProblem(sBenchmarkPath + "p.pddl", deadEndPath, domain);
            BeliefState bsInitial = problem.GetInitialBelief();

            string sOutput = "";

            sOutput = problem.Name + "\t" + DateTime.Now;
            DateTime dtBeforeTranslate = DateTime.Now;

            Process pCCF2CS = new Process();
            pCCF2CS.StartInfo.WorkingDirectory = sBenchmarkPath;
            pCCF2CS.StartInfo.FileName = sExePath + "ccf2cs";
            pCCF2CS.StartInfo.Arguments = "-t0 -cond -cod -cmr -csl -ckit -ckinl -cminl -cmit -cdisjk0 -cdisjm0 -mac  -cfc -fp -sn d.pddl p.pddl";
            pCCF2CS.StartInfo.UseShellExecute = false;
            if (RedirectShellOutput)
            {
                pCCF2CS.StartInfo.RedirectStandardOutput = true;
                pCCF2CS.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);
            }
            pCCF2CS.Start();
            if (RedirectShellOutput)
            {
                //string sOutput = p.StandardOutput.ReadToEnd();
                pCCF2CS.BeginOutputReadLine();
            }
            if (!pCCF2CS.WaitForExit(1000 * 60 * 30))//20 minutes max
            {
                pCCF2CS.Kill();
                m_mCLGMutex.WaitOne();
                StreamWriter sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
                sw.Write(sOutput + "\tcould not translate problem\n");
                sw.Close();
                m_mCLGMutex.ReleaseMutex();
                //throw new Exception("Could not translate problem");
                return;
            }

            sOutput += "\t" + (DateTime.Now - dtBeforeTranslate).TotalSeconds;

            int cFailures = 0;
            List<double> lActions = new List<double>();
            List<double> lTimes = new List<double>();

            for (int i = 1; i <= cAttempts; i++)
                File.Delete(sBenchmarkPath + i + ".hs");

            bool bLocalizeDomain = false;
            if (domain.Name.Contains("localize") || domain.Name.Contains("sliding-doors") || domain.Name.Contains("medical") || domain.Name.Contains("RockSample"))
                bLocalizeDomain = true;
            Debug.WriteLine("Done " + problem.Name + " translation");

            for (int i = 1; i <= cAttempts; i++)
            {
                DateTime dtStart = DateTime.Now;
                Debug.WriteLine("++++++++++++++++++++++++++++++++++++++++++++++++++++");
                State sChosen = null;
                Process pCLG = new Process();
                pCLG.StartInfo.WorkingDirectory = sBenchmarkPath;
                pCLG.StartInfo.FileName = sExePath + "CLG";
                pCLG.StartInfo.UseShellExecute = false;
                if (bLocalizeDomain)
                {
                    pCLG.StartInfo.Arguments = "-a 1 -f new-p.pddl -o new-d.pddl";
                }
                else
                {
                    pCLG.StartInfo.Arguments = "-a 1 -f new-p.pddl -o new-d.pddl" + " -w " + i + ".hs";
                    sChosen = bsInitial.WriteHiddenState(sBenchmarkPath + i + ".hs", false);
                }

                //pCLG.StartInfo.RedirectStandardOutput = true;
                Debug.WriteLine("Starting CLG");
                File.Delete(sBenchmarkPath + "CLGplan.txt");
                if (RedirectShellOutput)
                {
                    pCLG.StartInfo.RedirectStandardOutput = true;
                    pCLG.OutputDataReceived += new DataReceivedEventHandler(OutputHandler);
                }
                pCLG.Start();
                if (RedirectShellOutput)
                {
                    //string sOutput = p.StandardOutput.ReadToEnd();
                    pCLG.BeginOutputReadLine();
                }                 /*
                    StreamWriter swOutput = new StreamWriter(sBenchmarkPath + "CLGOutput.txt");
                    swOutput.Write(pCLG.StandardOutput.ReadToEnd());
                    swOutput.Close();                
                 * */
                if (!pCLG.WaitForExit(1000 * 60 * 30))//30 minutes max
                {
                    pCLG.Kill();
                    cFailures++;
                }
                else if (!File.Exists(sBenchmarkPath + "CLGplan.txt"))
                {
                    cFailures++;
                }
                else
                {
                    StreamReader sr = new StreamReader(sBenchmarkPath + "CLGplan.txt");
                    List<string> lPlan = new List<string>();
                    sr.ReadLine();//root
                    while (!sr.EndOfStream)
                    {
                        string sLine = sr.ReadLine();
                        string sParsedLine = sLine.Trim().ToLower().Replace("_", " ").
                            Replace("smell wumpus", "smell_wumpus").Replace("cd ", "cd_").Replace("my file", "my_file")
                            .Replace(" package ", "_package_").Replace(" truck ", "_truck_")
                            //.Replace(" airplane", "_airplane")
                            ;
                        lPlan.Add(sParsedLine);
                    }
                    sr.Close();
                    int cActions = 0;
                    TimeSpan tsTime;
                    bool bSuccess = true;
                    if (!bLocalizeDomain)
                        bSuccess = TestCLGPlan(sBenchmarkPath, domain, problem, lPlan, sChosen, out cActions, out tsTime, offline);
                    else
                        cActions = lPlan.Count;
                    if (!bSuccess)
                    {
                        cFailures++;
                        Debug.WriteLine("CLG Failed");
                    }
                    else
                    {
                        lActions.Add(cActions);
                        tsTime = DateTime.Now - dtStart;
                        lTimes.Add(tsTime.TotalSeconds);
                    }
                }
                Debug.WriteLine("Done " + problem.Name + " execution " + i + "/" + cAttempts);
            }

            m_mCLGMutex.WaitOne();
            StreamWriter sw1 = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw1.Write(sOutput);
            sw1.Close();
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\CLGResults.txt", lActions);
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\CLGResults.txt", lTimes);
            sw1 = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw1.WriteLine("\t" + cFailures);
            sw1.Close();
            m_mCLGMutex.ReleaseMutex();
            Debug.WriteLine("Done " + problem.Name);
        }


        static void TestCLGII(string sBenchmarkPath, int cAttempts, bool offline)
        {

            RandomGenerator.Init();
            string sExePath = BASE_PATH + @"\PDDL\CLG\";

            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sBenchmarkPath + "d.pddl");
            Problem problem = parser.ParseProblem(sBenchmarkPath + "p.pddl", deadEndPath, domain);
            BeliefState bsInitial = problem.GetInitialBelief();

            StreamWriter sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw.Write(problem.Name + "\t" + DateTime.Now);
            sw.Close();
            DateTime dtBeforeTranslate = DateTime.Now;

            Process pCCF2CS = new Process();
            pCCF2CS.StartInfo.WorkingDirectory = sBenchmarkPath;
            pCCF2CS.StartInfo.FileName = sExePath + "ccf2cs";
            pCCF2CS.StartInfo.Arguments = "-t0 -cond -cod -cmr -csl -ckit -ckinl -cminl -cmit -cdisjk0 -cdisjm0 -mac  -cfc -fp -sn d.pddl p.pddl";
            pCCF2CS.StartInfo.UseShellExecute = false;
            pCCF2CS.Start();
            if (!pCCF2CS.WaitForExit(1000 * 60 * 20))//20 minutes max
            {
                pCCF2CS.Kill();
                sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
                sw.Write("\tcould not translate problem\n");
                sw.Close();
                throw new Exception("Could not translate problem");
            }

            sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw.Write("\t" + (DateTime.Now - dtBeforeTranslate).TotalSeconds);
            sw.Close();

            int cFailures = 0;
            List<double> lActions = new List<double>();
            List<double> lTimes = new List<double>();

            for (int i = 1; i <= cAttempts; i++)
                File.Delete(sBenchmarkPath + i + ".hs");

            bool bLocalizeDomain = false;
            if (domain.Name.Contains("localize") || domain.Name.Contains("sliding-doors") || domain.Name.Contains("medical"))
                bLocalizeDomain = true;
            Debug.WriteLine("Done " + domain.Name + " translation");

            for (int i = 1; i <= cAttempts; i++)
            {
                DateTime dtStart = DateTime.Now;
                Debug.WriteLine("++++++++++++++++++++++++++++++++++++++++++++++++++++");
                State sChosen = null;
                Process pCLG = new Process();
                pCLG.StartInfo.WorkingDirectory = sBenchmarkPath;
                pCLG.StartInfo.FileName = sExePath + "CLG";
                pCLG.StartInfo.UseShellExecute = false;
                if (bLocalizeDomain)
                {
                    pCLG.StartInfo.Arguments = "-a 1 -f new-p.pddl -o new-d.pddl";
                }
                else
                {
                    pCLG.StartInfo.Arguments = "-a 1 -f new-p.pddl -o new-d.pddl" + " -w " + i + ".hs";
                    sChosen = bsInitial.WriteHiddenState(sBenchmarkPath + i + ".hs", false);
                }

                //pCLG.StartInfo.RedirectStandardOutput = true;
                Debug.WriteLine("Starting CLG");
                File.Delete(sBenchmarkPath + "CLGplan.txt");
                pCLG.Start();
                /*
                    StreamWriter swOutput = new StreamWriter(sBenchmarkPath + "CLGOutput.txt");
                    swOutput.Write(pCLG.StandardOutput.ReadToEnd());
                    swOutput.Close();                
                 * */
                if (!pCLG.WaitForExit(1000 * 60 * 20))//20 minutes max
                {
                    pCLG.Kill();
                    cFailures++;
                }
                else if (!File.Exists(sBenchmarkPath + "CLGplan.txt"))
                {
                    cFailures++;
                }
                else
                {
                    StreamReader sr = new StreamReader(sBenchmarkPath + "CLGplan.txt");
                    List<string> lPlan = new List<string>();
                    sr.ReadLine();//root
                    while (!sr.EndOfStream)
                    {
                        string sLine = sr.ReadLine();
                        string sParsedLine = sLine.Trim().ToLower().Replace("_", " ").
                            Replace("smell wumpus", "smell_wumpus").Replace("cd ", "cd_").Replace("my file", "my_file")
                            .Replace(" package ", "_package_").Replace(" truck ", "_truck_")
                            //.Replace(" airplane", "_airplane")
                            ;
                        lPlan.Add(sParsedLine);
                    }
                    sr.Close();
                    int cActions = 0;
                    TimeSpan tsTime;
                    bool bSuccess = true;
                    if (!bLocalizeDomain)
                        bSuccess = TestCLGPlan(sBenchmarkPath, domain, problem, lPlan, sChosen, out cActions, out tsTime, offline);
                    else
                        cActions = lPlan.Count;
                    if (!bSuccess)
                    {
                        cFailures++;
                        Debug.WriteLine("CLG Failed");
                    }
                    else
                    {
                        lActions.Add(cActions);
                        tsTime = DateTime.Now - dtStart;
                        lTimes.Add(tsTime.TotalSeconds);
                    }
                }
                Debug.WriteLine("Done " + domain.Name + " execution " + i);
            }

            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\CLGResults.txt", lActions);
            TestBenchmarkThread.WriteResultsToFile(sBenchmarkPath + @"..\CLGResults.txt", lTimes);
            sw = new StreamWriter(sBenchmarkPath + @"..\CLGResults.txt", true);
            sw.Write("\t" + cFailures + "\n");
            sw.Close();
            Debug.WriteLine("Done " + domain.Name);
        }

        static bool TestCLGPlan(string sPath, Domain domain, Problem problem, List<string> lPlan, State sChosen,
            out int cActions, out TimeSpan tsTime, bool offline)
        {
            DateTime dtStart = DateTime.Now;
            BeliefState bsInitial = problem.GetInitialBelief();
            bsInitial.UnderlyingEnvironmentState = sChosen;
            PartiallySpecifiedState pssCurrent = bsInitial.GetPartiallySpecifiedState(), pssNext = null;
            Formula fObserved = null;
            cActions = 0;
            foreach (string sAction in lPlan)
            {
                TimeSpan ts = DateTime.Now - dtStart;
                //if (ts.TotalMinutes > MaxTimePerProblem)
                //    throw new Exception("Execution taking too long");
                Debug.WriteLine((int)(ts.TotalMinutes) + "," + cActions + ") " + domain.Name + ", executing action " + sAction);
                Action a = domain.GroundActionByName(sAction.Split(' '));
                if (a.Observe != null)
                {
                    Predicate pObserve = ((PredicateFormula)a.Observe).Predicate;
                    if (pssCurrent.Observed.Contains(pObserve) || pssCurrent.Observed.Contains(pObserve.Negate()))
                        continue;
                }
                pssNext = pssCurrent.Apply(a, out fObserved);
                if (fObserved != null)
                {

                    Debug.WriteLine(domain.Name + ", observed " + fObserved);
                }
                if (pssNext == null)
                {
                    Debug.WriteLine(domain.Name + ", cannot execute " + sAction);
                    break;
                }
                cActions++;
                pssCurrent = pssNext;
            }
            tsTime = DateTime.Now - dtStart;
            if (pssCurrent.IsGoalState())
                Debug.WriteLine("Plan succeeded!");
            Debug.WriteLine("*******************************************************************************");
            return pssCurrent.IsGoalState();
        }

        /*
        static List<string> Plan(string sPath, BeliefState bsCurrent, out State sChosen)
        {
            sChosen = bsCurrent.WriteTaggedDomainAndProblem(sPath + "Kd.pddl", sPath + "Kp.pddl");
            File.Delete(sPath + "plan.txt");
            foreach (Process pFF in Process.GetProcesses())
            {
                if (pFF.ProcessName.ToLower().Contains("ff.exe"))
                    pFF.Kill();
            }
            Process p = new Process();
            p.StartInfo.WorkingDirectory = sPath;
            p.StartInfo.FileName = BASE_PATH + @"\PDDL\ff.exe";
            p.StartInfo.Arguments = "-o Kd.pddl -f Kp.pddl";
            p.StartInfo.UseShellExecute = false;
            p.Start();
            if (!p.WaitForExit(1000 * 60 * 2))//2 minutes max
                return null;
            StreamReader sr = new StreamReader(sPath + "plan.txt");
            List<string> lPlan = new List<string>();
            while (!sr.EndOfStream)
                lPlan.Add(sr.ReadLine().Trim().ToLower());
            sr.Close();
            return lPlan;
        }
        */
        private static void OutputHandler(object sendingProcess, DataReceivedEventArgs outLine)
        {
            //do nothing - not interested in the output
            //Debug.WriteLine(outLine.Data);
        }

        static int g_cObservations = 0, g_cUnexpectedObservations = 0, g_cGlobalActions = 0;
        /*
        static void WriteKnowledgeDomain(Domain domain, Problem problem, int iIteration)
        {
            string sPath = BASE_PATH + @"\PDDL\IPPC-domains\" + domain.Name + @"\" + problem.Name + @"\" + SDRPlanner.TagsCount + @"\";
            if (!Directory.Exists(sPath))
                Directory.CreateDirectory(sPath);
            Debug.WriteLine(domain.Name + "." + problem.Name + "." + SDRPlanner.TagsCount + "." + iIteration);
            //BeliefState.AddAllKnownToGiven = true;
            //SDRPlanner.AddTagRefutationToGoal = true;
            BeliefState bsInitial = problem.GetInitialBelief();
            State s = bsInitial.ChooseState(true);
            PartiallySpecifiedState pssCurrent = bsInitial.GetPartiallySpecifiedState();
            RandomGenerator.Init();
            int cTags = 0;
            State sChosen = pssCurrent.WriteTaggedDomainAndProblem(sPath + "Kd." + iIteration + ".pddl",
                                                                    sPath + "Kp." + iIteration + ".pddl", out cTags);
        }
        */
        static bool Equals(List<string> l1, List<string> l2)
        {
            if (l1.Count != l2.Count)
                return false;
            int i = 0;
            for (i = 0; i < l1.Count; i++)
            {
                if (l1[i] != l2[i])
                    return false;
            }
            return true;
        }
        class TestBenchmarkThread
        {
            public string BenchmarkPath { get; set; }
            public string Benchmark { get; set; }
            public int Trials { get; set; }
            public bool WriteResults { get; set; }

            public bool Online { get; set; }

            public int MaxTimePerProblem { get; set; }

            public DeadendStrategy DeadendStrategy { get; set; }

            private static Mutex m_mWriteToFile = new Mutex();

            public TestBenchmarkThread(string sBenchmarkPath, string sBenchmark, int cTrials, bool bWriteResults, bool bOnline, DeadendStrategy ds, int iMaxTimePerProblem)
            {
                BenchmarkPath = sBenchmarkPath;
                Benchmark = sBenchmark;
                Trials = cTrials;
                WriteResults = bWriteResults;
                Online = bOnline;
                DeadendStrategy = ds;
                MaxTimePerProblem = iMaxTimePerProblem;
            }

            public void Run()
            {
                if (UseCLG)
                    TestCLG(BenchmarkPath + Benchmark + "\\", Trials, true);
                else
                    TestBenchmark(BenchmarkPath, Benchmark, Trials, WriteResults, Online, DeadendStrategy, MaxTimePerProblem);
            }
            void TestBenchmark(string sBenchmarkPath, string sBenchmark, int cTrials, bool bWriteResults, bool bOnline, DeadendStrategy ds, int iTimePerProblem)
            {
                List<double> lTime = new List<double>();
                List<double> lActions = new List<double>();
                List<double> lPlanning = new List<double>();
                List<double> lObservations = new List<double>();
                int cFailure = 0;
                string sPath = sBenchmarkPath + sBenchmark + @"/";
                using (StreamWriter sw = new StreamWriter(sPath + "/" + ResultsFile, true))
                {
                    try
                    {
                        Debug.WriteLine("Reading domain and problem");
                        Parser parser = new Parser();
                        Domain domain = parser.ParseDomain(sPath + "d.pddl");
                        Problem problem = parser.ParseProblem(sPath + "p.pddl", sPath + "dead.pddl", domain);
                        Debug.WriteLine("Done reading domain and problem");
                        DateTime dtStart = DateTime.Now;
                        DateTime dtEnd = DateTime.Now;
                        sw.WriteLine(sBenchmark + "\t" + DateTime.Now + "\t" +
                            (dtEnd - dtStart).TotalSeconds + "\t" + SDRPlanner.TagsCount + "\t" + DeadendStrategy + "\t" + Online + "\t");
                        if (!bOnline)
                            cTrials = 1;
                        for (int i = 0; i < cTrials; i++)
                        {
                            DateTime dtStartTask = DateTime.Now;

                            SDRPlanner sdr = new SDRPlanner(sPath, deadEndPath, domain, problem, bOnline, ds);

                            bool bSampleDeadendState = false;
                            if (bOnline)
                                bSampleDeadendState = i >= cTrials / 2;
                            sdr.Data.SampleDeadendState = bSampleDeadendState;

                            Thread t = new Thread(sdr.Start);
                            t.Name = "Planning " + domain.Name;
                            t.Start();
                            bool bFailed = false;
                            if (!t.Join(new TimeSpan(0, iTimePerProblem, 0)))
                            //t.Join();
                            {
                                //if (!t.Join(100))
                                t.Abort();
                                t.Join();
                                Thread.Sleep(500);
                                cFailure++;
                                bFailed = true;
                            }

                            sdr.TerminateFFPRocesses(t);

                            SDRPlanner.ExecutionData data = sdr.Data;

                            TimeSpan ts = (DateTime.Now - dtStartTask);
                            if (data.Failure)
                            {
                                cFailure++;
                                bFailed = true;
                                if (bOnline == false)
                                    lTime.Add(ts.TotalSeconds);
                            }
                            else
                            {
                                lActions.Add(data.Actions);
                                lPlanning.Add(data.Planning);
                                lTime.Add(data.Time.TotalSeconds);
                                lObservations.Add(data.Observations);
                            }
                            sw.WriteLine(i + ": " + data.Actions + "\t" + data.Planning + "\t" + data.Time.TotalSeconds + "\t" + bFailed
                                + "\t" + data.InitialStateDeadend + "\t" + data.DeadendStrategy + "\t" + data.Observations);

                            Debug.WriteLine(sBenchmark + ", " + i + "/" + cTrials + ", " + Math.Round(ts.TotalMinutes) + ", failed? " + bFailed);

                            if (bFailed && ts.TotalMinutes < MaxTimePerProblem)
                                Debug.Write("*");
                        }

                    }
                    catch (Exception e)
                    {
                        sw.Write(e.Message);
                        Debug.WriteLine(e);
                    }


                }
                if (bWriteResults)
                {
                    m_mWriteToFile.WaitOne();
                    using (StreamWriter swFile = new StreamWriter(sBenchmarkPath + ResultsFile, true))
                    {
                        //StreamWriter swFile = new StreamWriter(@"C:\Users\lera\Desktop\DeadEnds" + ResultsFile, true);

                        //swFile.Write(sw.ToString());
                        swFile.Write(sBenchmark + "\t" + SDRPlanner.TagsCount + "\t" + DeadendStrategy + "\t" + Online + "\t");
                        swFile.Close();
                    }
                    //actions, planning, observations, time, failures (avg,stdev,max)
                    WriteResultsToFile(sBenchmarkPath + ResultsFile, lActions);
                    WriteResultsToFile(sBenchmarkPath + ResultsFile, lPlanning);
                    WriteResultsToFile(sBenchmarkPath + ResultsFile, lObservations);
                    WriteResultsToFile(sBenchmarkPath + ResultsFile, lTime);
                    using (StreamWriter swFile = new StreamWriter(sBenchmarkPath + ResultsFile, true))
                    {
                        //swFile = new StreamWriter(@"C:\Users\lera\Desktop\DeadEnds" + ResultsFile, true);
                        swFile.WriteLine("\t" + cFailure);
                        swFile.Close();
                    }
                    m_mWriteToFile.ReleaseMutex();
                }
            }
            public static void WriteResultsToFile(string sFile, List<double> l)
            {
                double dAvg = 0.0, dMax = 0.0, dStdev = 0.0;
                foreach (double x in l)
                {
                    dAvg += x;
                    if (x > dMax)
                        dMax = x;
                }
                dAvg /= l.Count;
                foreach (double x in l)
                {
                    dStdev += (x - dAvg) * (x - dAvg);
                }
                dStdev /= l.Count;
                dStdev = Math.Sqrt(dStdev);
                using (StreamWriter sw = new StreamWriter(sFile, true))
                {
                    //StreamWriter sw = new StreamWriter(@"C:\Users\lera\Desktop\DeadEnds\res.txt", true);
                    sw.Write("\t" + dAvg + "\t" + dStdev + "\t" + dMax);
                    sw.Close();
                }
            }
        }

        static Thread TestBenchmark(string sBenchmarkPath, string sBenchmark, int cTrials, bool bWriteResults, bool bSeparateThread, bool bOnline = true, DeadendStrategy ds = DeadendStrategy.Active, int iMaxTimePerProblem = 15)
        {
            TestBenchmarkThread tbt = new TestBenchmarkThread(sBenchmarkPath, sBenchmark, cTrials, bWriteResults, bOnline, ds, iMaxTimePerProblem);
            if (!bSeparateThread)
            {
                tbt.Run();
                return null;
            }
            else
            {
                Thread t = new Thread(tbt.Run);
                t.Name = "TestBenchmark " + sBenchmark;
                t.Start();
                return t;
            }
        }

        static void TestAllDeadend(string sBenchmarkPath, int cTrials, bool bMultiThread, string sDomainType = "")
        {
            List<DirectoryInfo> lBenchmarks = new List<DirectoryInfo>();
            HashSet<string> lDone = new HashSet<string>();
            DirectoryInfo dir = new DirectoryInfo(sBenchmarkPath);

            if (File.Exists(sBenchmarkPath + "/" + ResultsFile))
            {
                using (StreamReader sr = new StreamReader(sBenchmarkPath + "/" + ResultsFile))
                {
                    while (!sr.EndOfStream)
                    {
                        string sLine = sr.ReadLine();
                        string sDomain = sLine.Split('\t')[0];
                        lDone.Add(sDomain);
                    }
                    sr.Close();
                }
            }

            lBenchmarks = new List<DirectoryInfo>(dir.GetDirectories());


            foreach (DirectoryInfo subdir in lBenchmarks)
            {
                if (lDone.Contains(subdir.Name))
                    continue;

                if (sDomainType != "" && !subdir.Name.StartsWith(sDomainType))
                    continue;

                if (!File.Exists(subdir.FullName + "/d.pddl") || !File.Exists(subdir.FullName + "/p.pddl"))
                    continue;

                Debug.WriteLine("Writing deadend detection problem");

                Parser pr = new Parser();

                Domain d = pr.ParseDomain(subdir.FullName + "/d.pddl");
                Problem p = pr.ParseProblem(subdir.FullName + "/p.pddl", d);
                p.WriteDeadendDetectionProblem(subdir.FullName + "/tp.pddl");
                d.WriteDeadendDetectionDomain(subdir.FullName + "/td.pddl", p);

                if (File.Exists(subdir.FullName + "/results.txt"))
                    File.Delete(subdir.FullName + "/results.txt");


                TestBenchmark(sBenchmarkPath, subdir.Name, 1, true, bMultiThread, false, DeadendStrategy.Classical, 15);
                //TestBenchmark(sBenchmarkPath, subdir.Name, 1, true, bMultiThread, false, DeadendStrategy.Lazy, 15);
                //TestBenchmark(sBenchmarkPath, subdir.Name, 1, true, bMultiThread, false, DeadendStrategy.Both, 15);
                //TestBenchmark(sBenchmarkPath, subdir.Name, 1, true, bMultiThread, false, DeadendStrategy.Active, 15);
                /*
                TestBenchmark(sBenchmarkPath, subdir.Name, cTrials, true, bMultiThread, true, DeadendStrategy.Lazy, 5);
                TestBenchmark(sBenchmarkPath, subdir.Name, cTrials, true, bMultiThread, true, DeadendStrategy.Active, 5);
                TestBenchmark(sBenchmarkPath, subdir.Name, cTrials, true, bMultiThread, true, DeadendStrategy.Both, 5);
                */

            }
        }



        static void TestAll(string sBenchmarkPath, string[] asBenchmarks, int cTrials, bool bMultiThread, bool bOnline, bool bOffline)
        {
            // int cMaxThreads = 1;
            //Thread[] aThreads = new Thread[cMaxThreads];
            /*
            foreach (string sBenchmark in asBenchmarks)
            {
                try
                {
                    TestBenchmark(sBenchmarkPath, sBenchmark, cTrials, true, true);
                }
                catch (Exception e)
                {
                }
            }
             * */
            int i = 0;
            //while (i < cMaxThreads && i < asBenchmarks.Length)

            while (i < asBenchmarks.Length)
            {
                if (bOnline)
                    TestBenchmark(sBenchmarkPath, asBenchmarks[i], cTrials, true, bMultiThread, true);
                if (bOffline)
                    TestBenchmark(sBenchmarkPath, asBenchmarks[i], cTrials, true, bMultiThread, false);
                //Thread.Sleep(2000); 
                i++;

            }
            /*
            while (i < asBenchmarks.Length)
            {
                for (int j = 0 ; j < cMaxThreads ; j++)
                {
                    if (aThreads[j] == null || aThreads[j].Join(1000))
                    {
                        aThreads[j] = TestBenchmark(sBenchmarkPath, asBenchmarks[i], cTrials, true, bMultiThread);
                        i++;
                        break;
                    }
                }
            }
            
            foreach (Thread t in aThreads)
                if( t != null )
                    t.Join();
               */

        }
        static void TestAll(string sBenchmarkPath, string[] asBenchmarks, int cTrials, int cTags, bool bOnline, bool bOffline)
        {
            foreach (string sBenchmark in asBenchmarks)
            {
                try
                {
                    SDRPlanner.TagsCount = cTags;
                    if (cTags == -1)
                    {
                        if (sBenchmark.ToLower().StartsWith("wumpus"))
                            SDRPlanner.TagsCount = 5;
                        else
                            SDRPlanner.TagsCount = 3;
                    }
                    /*
                    if (sBenchmark.ToLower().StartsWith("medpks"))
                        BeliefState.AddAllKnownToGiven = true;
                    else
                        BeliefState.AddAllKnownToGiven = false;
                    */
                    SDRPlanner.AddAllKnownToGiven = true;

                    if (bOnline)
                        TestBenchmark(sBenchmarkPath, sBenchmark, cTrials, true, true, true);
                    if (bOffline)
                        TestBenchmark(sBenchmarkPath, sBenchmark, cTrials, true, true, false);

                    Debug.WriteLine(g_cUnexpectedObservations + "/" + g_cObservations + "/" + g_cGlobalActions);
                    g_cUnexpectedObservations = 0;
                    g_cObservations = 0;
                    g_cGlobalActions = 0;
                }
                catch (Exception e)
                {

                }
            }
        }
        static void TestDoors(string sBenchmarkPath, int cSize)
        {
            Doors mm = new Doors(cSize, 0);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 5;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = false;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            SDRPlanner.AddTagRefutationToGoal = true;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestMasterMind(string sBenchmarkPath, int cColors, int cPegs)
        {
            MasterMind mm = new MasterMind(cColors, cPegs, 0);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 6;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = false;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            SDRPlanner.AddTagRefutationToGoal = true;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestRockSample(string sBenchmarkPath, int iSize, int cRocks)
        {
            RockSample mm = new RockSample(iSize, cRocks, 0);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            //for (int cTags = 2; cTags <= 4; cTags++)
            {
                SDRPlanner.TagsCount = 20;
                //BeliefState.AddAllKnownToGiven = true;
                //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                SDRPlanner.SDR_OBS = false;
                TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            }
            //SDRPlanner.AddTagRefutationToGoal = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }


        static void TestElevators(string sBenchmarkPath, int cFloors, int cPeople)
        {
            /*
            RockSample mm = new RockSample(iSize, cRocks, 0);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            for (int cTags = 2; cTags <= 4; cTags++)
            {
                SDRPlanner.TagsCount = 2;
                //BeliefState.AddAllKnownToGiven = true;
                //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                SDRPlanner.SDR_OBS = false;
                TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            }
             * */
            //SDRPlanner.AddTagRefutationToGoal = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestCanadianTravelingSalesPerson(string sBenchmarkPath, int iLength, int iWidth, int iSensingCost)
        {
            CanadianTravelingSalesPerson ctsp = new CanadianTravelingSalesPerson(iLength, iWidth, iSensingCost);
            string sBenchmark = ctsp.Name;
            ctsp.WriteDomain(sBenchmarkPath + sBenchmark);
            ctsp.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 4;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = false;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestOmelette(string sBenchmarkPath, int cRequiredEggs)
        {
            Omelette o = new Omelette(cRequiredEggs);
            string sBenchmark = o.Name;
            o.WriteDomain(sBenchmarkPath + sBenchmark);
            o.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 3;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = true;
            TestBenchmark(sBenchmarkPath, sBenchmark, 3, true, false);
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestCatchInvaders(string sBenchmarkPath, int iSize, int cInvaders)
        {
            CatchtInvaders mm = new CatchtInvaders(iSize, cInvaders);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 5;
            SDRPlanner.AddTagRefutationToGoal = true;
            SDRPlanner.AddAllKnownToGiven = false;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 10, false, false);
        }
        static void TestWumpus(string sBenchmarkPath, int iSize)
        {
            SDRPlanner.AddAllKnownToGiven = true;
            //WumpusDomain mm = new WumpusDomain(iSize, 0, false, true);
            WumpusDomain mm = new WumpusDomain(iSize, false);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 5, false, false);
        }
        static void TestLargeWumpus(string sBenchmarkPath, int iSize)
        {
            double dDensity = 0.05;
            SDRPlanner.AddAllKnownToGiven = true;
            LargeWumpusDomain mm = new LargeWumpusDomain(iSize);
            LargeWumpusDomain.PitCount = (int)(dDensity * iSize * iSize);
            LargeWumpusDomain.WumpusCount = (int)(dDensity * iSize * iSize);
            string sBenchmark = mm.Name;
            mm.WriteDomain(sBenchmarkPath + sBenchmark);
            mm.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }
        static void TestBattleship(string sBenchmarkPath, int iSize)
        {
            SDRPlanner.AddAllKnownToGiven = true;
            Battleship bs = new Battleship(iSize * 10);
            string sBenchmark = bs.Name;
            bs.WriteDomain(sBenchmarkPath + sBenchmark);
            bs.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }
        static void TestMineSweeper(string sBenchmarkPath, int iSize)
        {
            SDRPlanner.AddAllKnownToGiven = true;
            MineSweeper ms = new MineSweeper(iSize);
            string sBenchmark = ms.Name;
            ms.WriteDomain(sBenchmarkPath + sBenchmark);
            ms.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            SDRPlanner.AddTagRefutationToGoal = false;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 2);
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestBoxes(string sBenchmarkPath, string sDomainFile)
        {
            BoxDomain bd = new BoxDomain(sBenchmarkPath + "\\Boxes\\" + sDomainFile);
            string sBenchmark = bd.Name;
            bd.WriteDomain(sBenchmarkPath + sBenchmark);
            bd.WriteProblem(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            //Domain.MAX_OPTIONS = 2;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
            SDRPlanner.SDR_OBS = false;
            SDRPlanner.AddTagRefutationToGoal = true;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }

        static void TestBoxeOpening(string sBenchmarkPath)
        {
            BoxOpening bo = new BoxOpening(6, 4);
            string sBenchmark = bo.Name;
            bo.WriteDomain(sBenchmarkPath + sBenchmark);
            bo.WriteProblem(sBenchmarkPath + sBenchmark);
            bo.WriteDeadends(sBenchmarkPath + sBenchmark);
            SDRPlanner.TagsCount = 2;
            //Domain.MAX_OPTIONS = 2;
            //BeliefState.AddAllKnownToGiven = true;
            //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
            SDRPlanner.SDR_OBS = true;
            SDRPlanner.AddTagRefutationToGoal = false;
            TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false, false);
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            //SDR_OBS = true;
            //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
        }
        static void TestWumpusDeadend(string sBenchmarkPath)
        {
            for (int i = 4; i <= 20; i++)
            {
                WumpusDeadends wd = new WumpusDeadends(i);
                string sBenchmark = wd.Name;
                wd.WriteDomain(sBenchmarkPath + sBenchmark);
                wd.WriteProblem(sBenchmarkPath + sBenchmark);
                wd.WriteDeadends(sBenchmarkPath + sBenchmark);


                Parser pr = new Parser();

                Domain d = pr.ParseDomain(sBenchmarkPath + sBenchmark + "/d.pddl");
                Problem p = pr.ParseProblem(sBenchmarkPath + sBenchmark + "/p.pddl", d);
                p.WriteDeadendDetectionProblem(sBenchmarkPath + sBenchmark + "/tp.pddl");
                d.WriteDeadendDetectionDomain(sBenchmarkPath + sBenchmark + "/td.pddl", p);


                SDRPlanner.TagsCount = 2;
                //Domain.MAX_OPTIONS = 2;
                //BeliefState.AddAllKnownToGiven = true;
                //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                SDRPlanner.SDR_OBS = true;
                SDRPlanner.AddTagRefutationToGoal = false;
                TestBenchmark(sBenchmarkPath, sBenchmark, 4, false, false, true);
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
                //SDR_OBS = true;
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            }
        }

        static void TestSokoban(string sBenchmarkPath)
        {
            for (int i = 14; i < 30; i++)
            {
                int cStones = i % 2 + 2;
                int cUncertain = cStones - 1;
                int cDeadends = cUncertain - 1;
                if (cDeadends == 0)
                    cDeadends = 1;
                Sokoban sd = new Sokoban(i / 5 + 4, cStones, cDeadends, cUncertain, i);
                string sBenchmark = sd.Name;
                sd.WriteDomain(sBenchmarkPath + sBenchmark);
                sd.WriteProblem(sBenchmarkPath + sBenchmark);
                sd.WriteDeadends(sBenchmarkPath + sBenchmark);
                SDRPlanner.TagsCount = 2;
                //Domain.MAX_OPTIONS = 2;
                //BeliefState.AddAllKnownToGiven = true;
                //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                SDRPlanner.SDR_OBS = true;
                SDRPlanner.AddTagRefutationToGoal = false;
                TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false, false);
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
                //SDR_OBS = true;
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            }
        }

        static void TestUnix(string sBenchmarkPath)
        {
            for (int i = 0; i < 30; i++)
            {
                int iDepth = i / 5 + 4;
                int iWidth = i % 3 + 2;
                int cFilePositions = 10 + i / 4;
                UnixDeadends ud = new UnixDeadends(iDepth, iWidth, cFilePositions, i);
                string sBenchmark = ud.Name;
                ud.WriteDomain(sBenchmarkPath + sBenchmark);
                ud.WriteProblem(sBenchmarkPath + sBenchmark);
                ud.WriteDeadends(sBenchmarkPath + sBenchmark);
                SDRPlanner.TagsCount = 2;



                Parser pr = new Parser();

                Domain d = pr.ParseDomain(sBenchmarkPath + sBenchmark + "/d.pddl");
                Problem p = pr.ParseProblem(sBenchmarkPath + sBenchmark + "/p.pddl", d);
                p.WriteDeadendDetectionProblem(sBenchmarkPath + sBenchmark + "/tp.pddl");
                d.WriteDeadendDetectionDomain(sBenchmarkPath + sBenchmark + "/td.pddl", p);

                //Domain.MAX_OPTIONS = 2;
                //BeliefState.AddAllKnownToGiven = true;
                //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                SDRPlanner.SDR_OBS = true;
                SDRPlanner.AddTagRefutationToGoal = false;
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false, false);
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
                //SDR_OBS = true;
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            }
        }


        static void TestBlocks(string sBenchmarkPath)
        {
            /*
            for (int i = 0; i < 30; i++)
            {
                int iSize = 10 + i / 3;
                int cHeavy = 4 + i / 3;
                int cHeavyArms = i % 3;
                BlocksworldDeadends ud = new BlocksworldDeadends(iSize, cHeavy, cHeavyArms, i);
                string sBenchmark = ud.Name;
                ud.WriteDomain(sBenchmarkPath + sBenchmark);
                ud.WriteProblem(sBenchmarkPath + sBenchmark);
                ud.WriteDeadends(sBenchmarkPath + sBenchmark);
                SDRPlanner.TagsCount = 2;



                Parser pr = new Parser();

                Domain d = pr.ParseDomain(sBenchmarkPath + sBenchmark + "/d.pddl");
                Problem p = pr.ParseProblem(sBenchmarkPath + sBenchmark + "/p.pddl", d);
                p.WriteDeadendDetectionProblem(sBenchmarkPath + sBenchmark + "/tp.pddl");
                d.WriteDeadendDetectionDomain(sBenchmarkPath + sBenchmark + "/td.pddl", p);

                //Domain.MAX_OPTIONS = 2;
                //BeliefState.AddAllKnownToGiven = true;
                //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                SDRPlanner.SDR_OBS = true;
                SDRPlanner.AddTagRefutationToGoal = false;
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false, false);
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
                //SDR_OBS = true;
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            }
            */
            for (int i = 1; i < 8; i++)
            {
                BlocksworldDeadends ud = new BlocksworldDeadends(15, 8, 1, 111, i);
                string sBenchmark = ud.Name;
                ud.WriteDomain(sBenchmarkPath + sBenchmark);
                ud.WriteProblem(sBenchmarkPath + sBenchmark);
                ud.WriteDeadends(sBenchmarkPath + sBenchmark);
                SDRPlanner.TagsCount = 2;

                ud = new BlocksworldDeadends(15, 8, 2, 111, i);
                sBenchmark = ud.Name;
                ud.WriteDomain(sBenchmarkPath + sBenchmark);
                ud.WriteProblem(sBenchmarkPath + sBenchmark);
                ud.WriteDeadends(sBenchmarkPath + sBenchmark);

            }
        }

        static void TestDoors(string sBenchmarkPath)
        {
            for (int iLength = 5; iLength <= 15; iLength += 2)
            {
                for (int iWidth = 3; iWidth <= iLength; iWidth += 2)
                {
                    DoorsDeadend ud = new DoorsDeadend(iLength, iWidth);
                    string sBenchmark = ud.Name;
                    ud.WriteDomain(sBenchmarkPath + sBenchmark);
                    ud.WriteProblem(sBenchmarkPath + sBenchmark);
                    ud.WriteDeadends(sBenchmarkPath + sBenchmark);
                    SDRPlanner.TagsCount = 2;



                    Parser pr = new Parser();

                    Domain d = pr.ParseDomain(sBenchmarkPath + sBenchmark + "/d.pddl");
                    Problem p = pr.ParseProblem(sBenchmarkPath + sBenchmark + "/p.pddl", d);
                    p.WriteDeadendDetectionProblem(sBenchmarkPath + sBenchmark + "/tp.pddl");
                    d.WriteDeadendDetectionDomain(sBenchmarkPath + sBenchmark + "/td.pddl", p);

                    //Domain.MAX_OPTIONS = 2;
                    //BeliefState.AddAllKnownToGiven = true;
                    //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                    SDRPlanner.SDR_OBS = true;
                    SDRPlanner.AddTagRefutationToGoal = false;
                    //TestBenchmark(sBenchmarkPath, sBenchmark, 4, false, false, true);
                    //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
                    //SDR_OBS = true;
                    //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
                }
            }
        }

        static void TestCavediving(string sBenchmarkPath)
        {
            int iSeed = 1;
            /*
            for (int iSize = 5; iSize <= 10; iSize++)
            {
                int cMaxSteps = 2;
                if (iSize >= 7)
                    cMaxSteps = 3;
                for (int iStep = 1; iStep <= cMaxSteps; iStep++)
                {
                    int cMaxPaths = 5;
                    if (iStep > 1)
                        cMaxPaths = 3;
                    for (int cPaths = 2; cPaths <= cMaxPaths; cPaths++)
                    {
                        //Cavediving cd = new Cavediving(5, 3, 2, 111);
                        Cavediving cd = new Cavediving(iSize, cPaths, iStep, iSeed);
                        string sBenchmark = cd.Name;
                        cd.WriteDomain(sBenchmarkPath + sBenchmark);
                        cd.WriteProblem(sBenchmarkPath + sBenchmark);
                        cd.WriteDeadends(sBenchmarkPath + sBenchmark);

                        Parser pr = new Parser();

                        Domain d = pr.ParseDomain(sBenchmarkPath + sBenchmark + "/d.pddl");
                        Problem p = pr.ParseProblem(sBenchmarkPath + sBenchmark + "/p.pddl", sBenchmarkPath + sBenchmark + "/dead.pddl", d);
                        p.WriteDeadendDetectionProblem(sBenchmarkPath + sBenchmark + "/tp.pddl");
                        d.WriteDeadendDetectionDomain(sBenchmarkPath + sBenchmark + "/td.pddl", p);
                        SDRPlanner.TagsCount = 2;
                        //Domain.MAX_OPTIONS = 2;
                        //BeliefState.AddAllKnownToGiven = true;
                        //TestCLG(sBenchmarkPath + sBenchmark + "\\", 10);
                        SDRPlanner.SDR_OBS = true;
                        SDRPlanner.AddTagRefutationToGoal = false;

                        iSeed++;

                    }
                }

                //bool bValid = SDRPlanner.CheckPlan(@"C:\LinuxApps\POPRP\src\plan.dot", d, p);


                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false, false);
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
                //SDR_OBS = true;
                //TestBenchmark(sBenchmarkPath, sBenchmark, 25, true, false);
            }
 */

            for (int i = 0; i < 4; i++)
            {
                int cPaths = 10;
                if (i >= 4)
                    cPaths = 4;
                if (i >= 6)
                    cPaths = 3;
                int iSize = 4 + i;
                Cavediving cd = new Cavediving(iSize, cPaths, 2, 0, -1);
                int cMaxDeadends = cd.Deadends.Count;
                for (int cDeadends = 1; cDeadends <= cMaxDeadends; cDeadends++)
                {
                    Console.WriteLine("Generating domain " + i + ", " + cDeadends);
                    cd = new Cavediving(iSize, 3, 2, 0, cDeadends);
                    string sBenchmark = cd.Name;
                    cd.WriteDomain(sBenchmarkPath + sBenchmark);
                    cd.WriteProblem(sBenchmarkPath + sBenchmark);
                    cd.WriteDeadends(sBenchmarkPath + sBenchmark);
                }
            }






        }

        static bool CheckPlan(string sBenchmarkPath, string sFileName, out int cNodes)
        {
            Parser pr = new Parser();
            Domain d = pr.ParseDomain(sBenchmarkPath + "/d.pddl");
            Problem p = pr.ParseProblem(sBenchmarkPath + "/p.pddl", sBenchmarkPath + "/dead.pddl", d);
            bool bValid = SDRPlanner.CheckPlan(sBenchmarkPath + "/" + sFileName, d, p, out cNodes);
            return bValid;
        }

        static void WriteDeadendDetection(string sPath, string sDomain)
        {
            Parser pr = new Parser();
            Domain d = pr.ParseDomain(sPath + "/" + sDomain + "/d.pddl");
            Problem p = pr.ParseProblem(sPath + "/" + sDomain + "/p.pddl", d);
            p.WriteDeadendDetectionProblem(sPath + "/" + sDomain + "/tp.pddl");
            d.WriteDeadendDetectionDomain(sPath + "/" + sDomain + "/td.pddl", p, true);

        }


        static void ProcessWoodworking(string sPath)
        {
            SDRPlanner.UseFilesForPlanners = true;
            DirectoryInfo d = new DirectoryInfo(sPath);
            FileInfo[] files = d.GetFiles("*.pddl");
            Dictionary<string, List<FileInfo>> dDomains = new Dictionary<string, List<FileInfo>>();
            foreach (FileInfo f in files)
            {
                string sName = f.Name.Substring(0, 3);
                if (!dDomains.ContainsKey(sName))
                    dDomains[sName] = new List<FileInfo>();
                dDomains[sName].Add(f);
            }
            foreach (string sName in dDomains.Keys)
            {
                string sWoodworking = "woodworking" + sName.Substring(1);
                if (Directory.Exists(d.FullName + "/" + sWoodworking))
                    continue;
                DirectoryInfo dSub = d.CreateSubdirectory(sWoodworking);
                Parser p = new Parser();
                p.IgnoreFunctions = true;
                Domain domain = null;
                Problem problem = null;

                foreach (FileInfo f in dDomains[sName])
                {
                    if (f.Name.Contains("domain"))
                        domain = p.ParseDomain(f.FullName);
                    else
                        problem = p.ParseProblem(f.FullName, domain);
                }

                ParametrizedPredicate pDefected = new ParametrizedPredicate("defected");
                pDefected.AddParameter(new Parameter("woodobj", "?w"));
                domain.AddPredicate(pDefected);

                foreach (Action a in domain.Actions)
                {
                    if (a is ParametrizedAction pa)
                    {
                        Parameter pBoard = null, pPart = null;
                        foreach (Parameter param in pa.Parameters)
                        {
                            if (param.Type == "board")
                                pBoard = param;
                            if (param.Type == "part")
                                pPart = param;
                        }
                        if (pBoard != null && pPart != null)
                        {
                            ParametrizedPredicate pBoardDefected = new ParametrizedPredicate("defected");
                            pBoardDefected.AddParameter(pBoard);
                            ParametrizedPredicate pPartDefected = new ParametrizedPredicate("defected");
                            pPartDefected.AddParameter(pPart);
                            CompoundFormula cfWhen = new CompoundFormula("when");
                            cfWhen.AddOperand(pBoardDefected);
                            cfWhen.AddOperand(pPartDefected);

                            ((CompoundFormula)a.Effects).AddOperand(cfWhen);
                        }
                    }
                }

                ParametrizedAction aObserveDefected = new ParametrizedAction("ObserveDefect");
                Parameter p1 = new Parameter("part", "?p");
                aObserveDefected.AddParameter(p1);
                ParametrizedPredicate pP1Defected = new ParametrizedPredicate("defected");
                pP1Defected.AddParameter(p1);
                //(surface-condition ?x smooth)
                //ParametrizedPredicate pP1Smooth = new ParametrizedPredicate("surface-condition");
                //pP1Smooth.AddParameter(p1);
                //pP1Smooth.AddParameter(new Constant("surface", "smooth"));
                //aObserveDefected.Preconditions = new PredicateFormula(pP1Smooth);

                ParametrizedPredicate pP1Avail = new ParametrizedPredicate("available");
                pP1Avail.AddParameter(p1);
                aObserveDefected.Preconditions = new PredicateFormula(pP1Avail);

                aObserveDefected.Observe = new PredicateFormula(pP1Defected);
                domain.AddAction(aObserveDefected);


                ParametrizedAction aDsiposePart = new ParametrizedAction("Dispose-Part");
                Parameter pColor = new Parameter("acolour", "?c");
                Parameter pSurface = new Parameter("surface", "?s");
                Parameter pTreatment = new Parameter("treatmentstatus", "?t");
                aDsiposePart.AddParameter(p1);
                aDsiposePart.AddParameter(pColor);
                aDsiposePart.AddParameter(pSurface);
                aDsiposePart.AddParameter(pTreatment);

                ParametrizedPredicate pP1Unused = new ParametrizedPredicate("unused");
                pP1Unused.AddParameter(p1);

                ParametrizedPredicate ppColor = new ParametrizedPredicate("colour");
                ppColor.AddParameter(p1);
                ppColor.AddParameter(pColor);

                ParametrizedPredicate ppSurface = new ParametrizedPredicate("surface-condition");
                ppSurface.AddParameter(p1);
                ppSurface.AddParameter(pSurface);

                ParametrizedPredicate ppTreatment = new ParametrizedPredicate("treatment");
                ppTreatment.AddParameter(p1);
                ppTreatment.AddParameter(pTreatment);

                CompoundFormula cfPre = new CompoundFormula("and");
                cfPre.AddOperand(pP1Unused.Negate());
                cfPre.AddOperand(ppColor);
                cfPre.AddOperand(ppSurface);
                cfPre.AddOperand(ppTreatment);
                aDsiposePart.Preconditions = cfPre;

                CompoundFormula cfEff = new CompoundFormula("and");
                cfEff.AddOperand(pP1Unused);
                cfEff.AddOperand(pP1Avail.Negate());
                cfEff.AddOperand(pP1Defected.Negate());
                cfEff.AddOperand(ppColor.Negate());
                cfEff.AddOperand(ppSurface.Negate());
                cfEff.AddOperand(ppTreatment.Negate());
                aDsiposePart.Effects = cfEff;

                domain.AddAction(aDsiposePart);

                HashSet<Constant> hsWoods = new HashSet<Constant>();
                Constant cMaxSize = null;
                foreach (Constant c in domain.Constants)
                {
                    if (c.Type == "awood")
                    {
                        hsWoods.Add(c);
                    }
                    if (c.Type == "aboardsize")
                        cMaxSize = c;
                }
                if (true)//set one board per type
                {
                    List<Predicate> lKnown = new List<Predicate>(problem.Known);
                    foreach (GroundedPredicate gp in lKnown)
                    {
                        bool bRemove = false;
                        foreach (Constant c in gp.Constants)
                        {
                            if (c.Type == "board")
                            {
                                bRemove = true;
                                domain.Constants.Remove(c);
                            }
                        }
                        if (bRemove)
                            problem.RemoveKnown(gp);
                    }
                    foreach (Constant cWood in hsWoods)
                    {
                        Constant cNewBoard = new Constant("board", "b-" + cWood.Name);
                        domain.Constants.Add(cNewBoard);

                        GroundedPredicate gpWood = new GroundedPredicate("wood");
                        gpWood.AddConstant(cNewBoard);
                        gpWood.AddConstant(cWood);
                        problem.AddKnown(gpWood);

                        GroundedPredicate gpWoodRough = new GroundedPredicate("surface-condition");
                        gpWoodRough.AddConstant(cNewBoard);
                        gpWoodRough.AddConstant(new Constant("surface", "rough"));
                        problem.AddKnown(gpWoodRough);

                        GroundedPredicate gpWoodSize = new GroundedPredicate("boardsize");
                        gpWoodSize.AddConstant(cNewBoard);
                        gpWoodSize.AddConstant(cMaxSize);
                        problem.AddKnown(gpWoodSize);

                        GroundedPredicate gpWoodAvailable = new GroundedPredicate("available");
                        gpWoodAvailable.AddConstant(cNewBoard);
                        problem.AddKnown(gpWoodAvailable);

                    }

                }

                HashSet<Predicate> hsGoal = problem.Goal.GetAllPredicates();
                Dictionary<Constant, Constant> dGoalWood = new Dictionary<Constant, Constant>();
                HashSet<Constant> hsParts = new HashSet<Constant>();
                foreach (GroundedPredicate gp in hsGoal)
                {
                    if (gp.Name == "wood")
                        dGoalWood[gp.Constants[0]] = gp.Constants[1];
                    foreach (Constant c in gp.Constants)
                    {
                        if (c.Type == "part")
                            hsParts.Add(c);
                    }
                }

                CompoundFormula cfGoal = new CompoundFormula("and");
                cfGoal.AddOperand(problem.Goal);
                foreach (Constant cPart in hsParts)
                {
                    GroundedPredicate gpDefected = new GroundedPredicate("defected");
                    gpDefected.AddConstant(cPart);
                    cfGoal.AddOperand(gpDefected.Negate());
                }
                problem.Goal = cfGoal;

                Dictionary<Constant, Constant> dBoardToWood = new Dictionary<Constant, Constant>();
                foreach (GroundedPredicate gp in problem.Known)
                {
                    if (gp.Name == "wood" && !gp.Negation)
                    {
                        dBoardToWood[gp.Constants[0]] = gp.Constants[1];
                    }
                }

                HashSet<Constant> hsBoards = new HashSet<Constant>();
                foreach (Constant c in domain.Constants)
                {
                    if (c.Type == "board")
                    {
                        hsBoards.Add(c);
                    }
                }



                foreach (Constant c in domain.Constants)
                {
                    if (c.Type == "board")
                    {
                        GroundedPredicate gpDefected = new GroundedPredicate("defected");
                        gpDefected.AddConstant(c);
                        CompoundFormula cfOr = new CompoundFormula("or");
                        cfOr.SimpleAddOperand(gpDefected);
                        cfOr.SimpleAddOperand(gpDefected.Negate());
                        problem.AddHidden(cfOr);
                    }
                }

                CompoundFormula cfDeadendOr = new CompoundFormula("or");
                foreach (Constant cPart in dGoalWood.Keys)
                {
                    bool bPossibleDeadend = true;
                    if (dBoardToWood.ContainsKey(cPart))
                        if (dBoardToWood[cPart] == dGoalWood[cPart])
                            bPossibleDeadend = false;
                    if (bPossibleDeadend)
                    {
                        CompoundFormula cfDeadendAnd = new CompoundFormula("and");
                        foreach (Constant cBoard in hsBoards)
                        {
                            if (dBoardToWood[cBoard] == dGoalWood[cPart])
                            {
                                GroundedPredicate gpDefected = new GroundedPredicate("defected");
                                gpDefected.AddConstant(cBoard);
                                cfDeadendAnd.AddOperand(gpDefected);
                            }
                        }
                        cfDeadendOr.AddOperand(cfDeadendAnd);
                    }
                }




                domain.WriteSimpleDomain(dSub.FullName + "/d.pddl", true, false);


                problem.WriteProblem(dSub.FullName + "/p.pddl");

                StreamWriter swDeadends = new StreamWriter(dSub.FullName + "/dead.pddl");
                swDeadends.WriteLine("(define (problem woodworking)");
                swDeadends.WriteLine("\t(:domain woodworking)");
                swDeadends.WriteLine("\t(:init");
                foreach (Formula f in cfDeadendOr.Operands)
                    swDeadends.WriteLine("\t" + f);
                swDeadends.WriteLine("))");
                swDeadends.Close();


                WriteDeadendDetection(d.FullName + "/", dSub.Name);


                //TestBenchmark(d.FullName + "/", dSub.Name, 4, false, false, true);
            }
        }


        static void ParseResults(string sPath, bool bWriteOffline, bool bWriteOnline)
        {
            StreamReader sr = new StreamReader(sPath + "/Results.txt");
            Dictionary<string, Dictionary<string, Dictionary<string, Dictionary<string, List<string>>>>> dResults = new Dictionary<string, Dictionary<string, Dictionary<string, Dictionary<string, List<string>>>>>();
            List<string> lProblems = new List<string>();
            while (!sr.EndOfStream)
            {
                string sLine = sr.ReadLine().Trim();
                if (sLine != "")
                {
                    string[] a = sLine.Split('\t');
                    if (!dResults.ContainsKey(a[0]))
                    {
                        string sProblem = a[0];
                        lProblems.Add(sProblem);
                        string sDomain = CleanNumbers(sProblem);
                        if (!dResults.ContainsKey(sDomain))
                        {
                            dResults[sDomain] = new Dictionary<string, Dictionary<string, Dictionary<string, List<string>>>>();
                            dResults[sDomain]["offline"] = new Dictionary<string, Dictionary<string, List<string>>>();
                            dResults[sDomain]["online"] = new Dictionary<string, Dictionary<string, List<string>>>();
                            dResults[sDomain]["offline"]["active"] = new Dictionary<string, List<string>>();
                            dResults[sDomain]["offline"]["lazy"] = new Dictionary<string, List<string>>();
                            dResults[sDomain]["offline"]["both"] = new Dictionary<string, List<string>>();
                            dResults[sDomain]["online"]["active"] = new Dictionary<string, List<string>>();
                            dResults[sDomain]["online"]["lazy"] = new Dictionary<string, List<string>>();
                            dResults[sDomain]["online"]["both"] = new Dictionary<string, List<string>>();
                        }
                        string sOnline = "online";
                        if (a[3] == "False")
                            sOnline = "offline";
                        string sMethod = a[2].ToLower();
                        List<string> lValues = new List<string>();
                        for (int i = 4; i < a.Length; i++)
                            lValues.Add(a[i]);
                        dResults[sDomain][sOnline][sMethod][sProblem] = lValues;
                    }
                }
            }

            if (bWriteOnline)
            {
                //Read online results for each run
                Dictionary<string, Dictionary<string, Dictionary<string, List<List<string>>>>> dOnlineRuns = new Dictionary<string, Dictionary<string, Dictionary<string, List<List<string>>>>>();
                foreach (string sProblem in lProblems)
                {
                    try
                    {
                        string sDomain = CleanNumbers(sProblem);
                        if (!dOnlineRuns.ContainsKey(sDomain))
                            dOnlineRuns[sDomain] = new Dictionary<string, Dictionary<string, List<List<string>>>>();
                        dOnlineRuns[sDomain][sProblem] = new Dictionary<string, List<List<string>>>();
                        StreamReader srLocalResults = new StreamReader(sPath + "/" + sProblem + "/Results.txt");
                        while (!srLocalResults.EndOfStream)
                        {
                            string sLine = srLocalResults.ReadLine();
                            string[] a = sLine.Split(new char[] { '\t', ':' });
                            if (a[0] != sProblem)
                            {
                                //i + ": " + data.Actions + "\t" + data.Planning + "\t" + data.Time.TotalSeconds + "\t" + bFailed +"\t" + data.InitialStateDeadend + "\t" + data.DeadendStrategy + "\t" + data.Observations
                                string sStrategy = a[6];
                                if (!dOnlineRuns[sDomain][sProblem].ContainsKey(sStrategy))
                                    dOnlineRuns[sDomain][sProblem][sStrategy] = new List<List<string>>();
                                dOnlineRuns[sDomain][sProblem][sStrategy].Add(new List<string>(a));
                            }
                        }
                    }
                    catch (Exception e)
                    { }
                }


                using (StreamWriter swSuccess = new StreamWriter(sPath + "/" + "OnlineSuccess.csv"))
                {
                    foreach (string sDomain in dOnlineRuns.Keys)
                    {
                        swSuccess.Write(sDomain);
                        foreach (string sStrategy in dOnlineRuns[sDomain].First().Value.Keys)
                        {
                            double cDeadend = 0, cSolvable = 0;
                            int cSuccessDeadend = 0, cSuccessSolvable = 0;
                            foreach (string sProblem in dOnlineRuns[sDomain].Keys)
                            {
                                try
                                {
                                    foreach (List<string> lValues in dOnlineRuns[sDomain][sProblem][sStrategy])
                                    {
                                        bool bDeaend = lValues[5] == "True";
                                        bool bSuccess = lValues[4] == "False";
                                        if (bDeaend)
                                        {
                                            cDeadend++;
                                            if (bSuccess)
                                            {
                                                cSuccessDeadend++;
                                            }
                                        }
                                        else
                                        {
                                            cSolvable++;
                                            if (bSuccess)
                                            {
                                                cSuccessSolvable++;
                                            }
                                        }
                                    }
                                }
                                catch (Exception e)
                                { }

                            }
                            swSuccess.Write("\t&\t" + Math.Round(cSuccessSolvable / cSolvable, 2) * 100 + @"\%");
                            swSuccess.Write("\t&\t" + Math.Round(cSuccessDeadend / cDeadend, 4) * 100 + @"\%");
                        }
                        swSuccess.WriteLine("\t" + @"\\ \hline");
                    }
                    swSuccess.Close();
                }


                using (StreamWriter swOnlineTime = new StreamWriter(sPath + "/" + "OnlineTime.csv"))
                {
                    foreach (string sDomain in dOnlineRuns.Keys)
                    {
                        swOnlineTime.Write(sDomain);
                        foreach (string sStrategy in dOnlineRuns[sDomain].First().Value.Keys)
                        {
                            double cDeadend = 0, cSolvable = 0;
                            double cSuccessDeadend = 0, cSuccessSolvable = 0;
                            double dTimeDeadend = 0, dTimeSolvable = 0;
                            foreach (string sProblem in dOnlineRuns[sDomain].Keys)
                            {
                                try
                                {
                                    foreach (List<string> lValues in dOnlineRuns[sDomain][sProblem][sStrategy])
                                    {
                                        bool bDeaend = lValues[5] == "True";
                                        bool bSuccess = lValues[4] == "False";
                                        if (bDeaend)
                                        {
                                            cDeadend++;
                                            if (bSuccess)
                                            {
                                                cSuccessDeadend++;
                                                //cActionsDeadend += int.Parse(lValues[1]);
                                                dTimeDeadend += double.Parse(lValues[3]);
                                            }
                                        }
                                        else
                                        {
                                            cSolvable++;
                                            if (bSuccess)
                                            {
                                                cSuccessSolvable++;
                                                //cActionsSolvable += int.Parse(lValues[1]);
                                                dTimeSolvable += double.Parse(lValues[3]);
                                            }
                                        }
                                    }
                                }
                                catch (Exception e)
                                { }

                            }
                            swOnlineTime.Write("\t&\t" + Math.Round(dTimeSolvable / cSuccessSolvable, 2));
                            swOnlineTime.Write("\t&\t" + Math.Round(dTimeDeadend / cSuccessDeadend, 2));
                            swOnlineTime.Write("\t&\t" + Math.Round((dTimeSolvable / cSuccessSolvable) / (dTimeDeadend / cSuccessDeadend), 2));
                        }
                        swOnlineTime.WriteLine("\t" + @"\\ \hline");
                    }
                    swOnlineTime.Close();
                }


                using (StreamWriter swOnlineActions = new StreamWriter(sPath + "/" + "OnlineActions.csv"))
                {
                    foreach (string sDomain in dOnlineRuns.Keys)
                    {
                        swOnlineActions.Write(sDomain);
                        foreach (string sStrategy in dOnlineRuns[sDomain].First().Value.Keys)
                        {
                            double cDeadend = 0, cSolvable = 0;
                            double cSuccessDeadend = 0, cSuccessSolvable = 0;
                            double cActionsDeadend = 0, cActionsSolvable = 0;
                            foreach (string sProblem in dOnlineRuns[sDomain].Keys)
                            {
                                try
                                {
                                    foreach (List<string> lValues in dOnlineRuns[sDomain][sProblem][sStrategy])
                                    {
                                        bool bDeaend = lValues[5] == "True";
                                        bool bSuccess = lValues[4] == "False";
                                        if (bDeaend)
                                        {
                                            cDeadend++;
                                            if (bSuccess)
                                            {
                                                cSuccessDeadend++;
                                                cActionsDeadend += int.Parse(lValues[1]);
                                                //dTimeDeadend += double.Parse(lValues[3]);
                                            }
                                        }
                                        else
                                        {
                                            cSolvable++;
                                            if (bSuccess)
                                            {
                                                cSuccessSolvable++;
                                                cActionsSolvable += int.Parse(lValues[1]);
                                                //dTimeSolvable += double.Parse(lValues[3]);
                                            }
                                        }
                                    }
                                }
                                catch (Exception e)
                                { }

                            }
                            swOnlineActions.Write("\t&\t" + Math.Round(cActionsSolvable / cSuccessSolvable, 2));
                            swOnlineActions.Write("\t&\t" + Math.Round(cActionsDeadend / cSuccessDeadend, 2));
                            swOnlineActions.Write("\t&\t" + Math.Round((cActionsSolvable / cSuccessSolvable) / (cActionsDeadend / cSuccessDeadend), 2));
                        }
                        swOnlineActions.WriteLine("\t" + @"\\ \hline");
                    }
                    swOnlineActions.Close();
                }

                foreach (string sDomain in dOnlineRuns.Keys)
                {
                    StreamWriter swDomain = new StreamWriter(sPath + "/" + sDomain + "Online.csv");
                    foreach (string sProblem in dOnlineRuns[sDomain].Keys)
                    {
                        string sProblemName = sProblem.Replace(sDomain, "").Replace("_", "&").Replace("-", "&").Replace("&", "\t&\t");
                        swDomain.Write(sProblemName);
                        foreach (string sStrategy in dOnlineRuns[sDomain][sProblem].Keys)
                        {
                            double cDeadend = 0, cSolvable = 0;
                            int cActionsDeadend = 0, cActionsSolvable = 0;
                            double dTimeDeadend = 0, dTimeSolvable = 0;
                            double cSuccessDeadend = 0, cSuccessSolvable = 0;

                            foreach (List<string> lValues in dOnlineRuns[sDomain][sProblem][sStrategy])
                            {
                                bool bDeaend = lValues[5] == "True";
                                bool bSuccess = lValues[4] == "False";
                                if (bDeaend)
                                {
                                    cDeadend++;
                                    if (bSuccess)
                                    {
                                        cSuccessDeadend++;
                                        cActionsDeadend += int.Parse(lValues[1]);
                                        dTimeDeadend += double.Parse(lValues[3]);
                                    }
                                }
                                else
                                {
                                    cSolvable++;
                                    if (bSuccess)
                                    {
                                        cSuccessSolvable++;
                                        cActionsSolvable += int.Parse(lValues[1]);
                                        dTimeSolvable += double.Parse(lValues[3]);
                                    }
                                }
                            }
                            if (cSuccessDeadend > 0 && cSuccessSolvable > 0)
                            {
                                double dTimeRatio = (dTimeSolvable / cSuccessSolvable) / (dTimeDeadend / cSuccessDeadend);
                                double dActionRatio = (cActionsSolvable / cSuccessSolvable) / (cActionsDeadend / cSuccessDeadend);
                                /*
                                swDomain.Write("\t&\t" + Math.Round(cSuccessSolvable / cSolvable, 2) * 100 + @"\%"  );
                                swDomain.Write("\t&\t" + Math.Round(dTimeSolvable / cSolvable, 2) );

                                swDomain.Write("\t&\t" + Math.Round(cSuccessDeadend / cDeadend, 4) * 100 + @"\%");
                                swDomain.Write("\t&\t" + Math.Round(dTimeDeadend / cDeadend, 2) );
                                */
                                swDomain.Write("\t&\t" + Math.Round(dTimeRatio, 2) + "\t&\t" + Math.Round(dActionRatio, 2));
                            }
                            else
                            {
                                if (cSuccessDeadend > 0)
                                {
                                    swDomain.Write("\t&\t" + "0/" + Math.Round(dTimeDeadend / cSuccessDeadend, 2) + "\t&\t" + "0/" + Math.Round(cActionsDeadend / cSuccessDeadend, 2));
                                }
                                if (cSuccessSolvable > 0)
                                {
                                    swDomain.Write("\t&\t" + Math.Round(dTimeSolvable / cSuccessSolvable, 2) + "/0" + "\t&\t" + Math.Round(cActionsSolvable / cSuccessSolvable, 2) + "/0");

                                }
                            }
                        }
                        swDomain.WriteLine("\t" + @"\\ \hline");
                    }

                    swDomain.Close();
                }
            }




            //coverage
            Dictionary<string, int> dProblemCount = new Dictionary<string, int>();
            Dictionary<string, Dictionary<string, int>> dOnlineCoverage = new Dictionary<string, Dictionary<string, int>>();
            Dictionary<string, Dictionary<string, int>> dOfflineCoverage = new Dictionary<string, Dictionary<string, int>>();
            foreach (string sDomain in dResults.Keys)
            {
                dOnlineCoverage[sDomain] = new Dictionary<string, int>();
                dOfflineCoverage[sDomain] = new Dictionary<string, int>();
                foreach (string sMethod in dResults[sDomain]["online"].Keys)
                {
                    dProblemCount[sDomain] = dResults[sDomain]["online"][sMethod].Keys.Count;
                    int cSolved = 0;
                    foreach (string sProblem in dResults[sDomain]["online"][sMethod].Keys)
                    {
                        if (dResults[sDomain]["online"][sMethod][sProblem].Last() == "0")
                            cSolved++;
                    }
                    dOnlineCoverage[sDomain][sMethod] = cSolved;
                }

                foreach (string sMethod in dResults[sDomain]["offline"].Keys)
                {
                    dProblemCount[sDomain] = dResults[sDomain]["offline"][sMethod].Keys.Count;
                    int cSolved = 0, cNotSolved = 0;
                    foreach (string sProblem in dResults[sDomain]["offline"][sMethod].Keys)
                    {
                        if (dResults[sDomain]["offline"][sMethod][sProblem][1].ToLower() != "nan")
                            cSolved++;
                        else
                            cNotSolved++;
                    }
                    dOfflineCoverage[sDomain][sMethod] = cSolved;
                }
            }

            StreamWriter swCoverage = new StreamWriter(sPath + "/Coverage.csv");
            foreach (string sDomain in dProblemCount.Keys)
            {
                swCoverage.Write(sDomain + "\t&\t" + dProblemCount[sDomain]);
                foreach (string sMethod in dOfflineCoverage[sDomain].Keys)
                    swCoverage.Write("\t&\t" + dOfflineCoverage[sDomain][sMethod]);
                foreach (string sMethod in dOnlineCoverage[sDomain].Keys)
                    swCoverage.Write("\t&\t" + dOnlineCoverage[sDomain][sMethod]);
                swCoverage.WriteLine("\t\\\\hline");
            }
            swCoverage.Close();



            StreamReader srPOPRP = new StreamReader(sPath + "/poprp.results.txt");
            Dictionary<string, List<string>> dPOPRP = new Dictionary<string, List<string>>();
            while (!srPOPRP.EndOfStream)
            {
                string sLine = srPOPRP.ReadLine();
                string[] aLine = sLine.Split(',');
                List<string> lValues = new List<string>();
                string sProblemName = aLine[0];
                foreach (string s in aLine)
                    if (s != sProblemName)
                        lValues.Add(s);
                dPOPRP[sProblemName] = lValues;
            }
            srPOPRP.Close();


            if (bWriteOffline)
            {
                //Offline per domain: time, graph size
                foreach (string sDomain in dProblemCount.Keys)
                {
                    StreamWriter swDomain = new StreamWriter(sPath + "/" + sDomain + "Offline.csv");
                    //swDomain.WriteLine("\t&\tActive\t&\t&\tLazy\t&\t&\tBoth\t&\t&");
                    //swDomain.WriteLine("Name\t&\tSize\t&\tTime\t&\tSize\t&\tTime\t&\tSize\t&\tTime\t&");
                    swDomain.WriteLine("Name\t&\tActive\t&\tLazy\t&\tA/L\t&\tPOPRP\t&\tActive\t&\tLazy \t&\tA/L\t&\tPOPRP\t  \\\\ \\hline");
                    List<string> lDomainProblems = new List<string>(dResults[sDomain]["offline"]["lazy"].Keys);
                    foreach (string sProblem in lDomainProblems)
                    {
                        List<double> lTime = new List<double>();
                        List<int> lSize = new List<int>();
                        foreach (string sMethod in dResults[sDomain]["offline"].Keys)
                        {
                            List<string> lValues = dResults[sDomain]["offline"][sMethod][sProblem];
                            //actions, planning, observations, time, failures (avg,stdev,max)
                            if (lValues[1] == "NaN")
                            {
                                double dTime = double.Parse(lValues[10]);
                                if (dTime >= 900)
                                {
                                    lTime.Add(1111);
                                    lSize.Add(1111);
                                }
                                else
                                {
                                    lTime.Add(2222);
                                    lSize.Add(2222);
                                }
                            }
                            else
                            {
                                lTime.Add(double.Parse(lValues[10]));
                                lSize.Add(int.Parse(lValues[1]));
                            }
                        }
                        if (dPOPRP.ContainsKey(sProblem))
                        {
                            List<string> lPOPRP = dPOPRP[sProblem];
                            if (lPOPRP[0].ToLower() == "false")
                            {
                                lTime.Add(1111);
                                lSize.Add(1111);
                            }
                            else
                            {
                                lTime.Add(double.Parse(lPOPRP[4]));
                                lSize.Add(int.Parse(lPOPRP[1]));
                            }
                        }

                        int iMinSize = lSize.Min();
                        double dMinTime = lTime.Min();


                        string sProblemName = sProblem.Replace(sDomain, "").Replace("_", "&").Replace("-", "&").Replace("&", "\t&\t");

                        swDomain.Write(sProblemName);

                        foreach (double dTime in lTime)
                        {
                            swDomain.Write("\t&\t");
                            if (dTime == dMinTime)
                                swDomain.Write("\\bf{");
                            if (dTime == 1111)
                            {
                                swDomain.Write("TO");
                            }
                            else if (dTime == 2222)
                            {
                                swDomain.Write("TTO");
                            }
                            else
                                swDomain.Write(Math.Round(dTime, 2));
                            if (dTime == dMinTime)
                                swDomain.Write("}");
                        }
                        foreach (int iSize in lSize)
                        {
                            swDomain.Write("\t&\t");
                            if (iSize == iMinSize)
                                swDomain.Write("\\bf{");
                            if (iSize == 1111)
                            {
                                swDomain.Write("TO");
                            }
                            else if (iSize == 2222)
                            {
                                swDomain.Write("TTO");
                            }
                            else
                                swDomain.Write(iSize);
                            if (iSize == iMinSize)
                                swDomain.Write("}");
                        }

                        swDomain.WriteLine("\t \\\\ \\hline");
                    }
                    swDomain.Close();
                }
            }
        }



        private static string CleanNumbers(string sProblem)
        {
            string s = "";
            foreach (char c in sProblem)
            {
                if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z'))
                    s += c;
            }
            return s;
        }


        public static List<string> ManualSolve(string sPath, string sDomain, string sProblem)
        {
            Parser parser = new Parser();
            Domain dK = parser.ParseDomain(sPath + "/" + sDomain);
            Problem pK = parser.ParseProblem(sPath + "/" + sProblem, "", dK);

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
            return lActionNames;
        }

        public static void ValidateAndCollectPOPRP(string sPath)
        {
            DirectoryInfo dir = new DirectoryInfo(sPath);
            File.Delete(sPath + "/poprp.results.txt");
            foreach (DirectoryInfo dSub in dir.GetDirectories())
            {
                bool bValid = false;
                int cNodes = 0;
                if (File.Exists(dSub.FullName + "/poprp.plan.dot"))
                {
                    bValid = CheckPlan(dSub.FullName, "poprp.plan.dot", out cNodes);
                }
                TimeSpan tsTranslation = new TimeSpan(0), tsPRP = new TimeSpan(0), tsTotal = new TimeSpan(0);
                if (File.Exists(dSub.FullName + "/poprp.time.txt"))
                {
                    using (StreamReader sr = new StreamReader(dSub.FullName + "/poprp.time.txt"))
                    {
                        string sLine = sr.ReadLine();
                        sLine = sLine.Replace("Elapsed time: ", "");
                        string[] a = sLine.Split(new char[] { ',' });
                        DateTime dtStart = DateTime.Parse(a[0]);
                        DateTime dtTranslation = DateTime.Parse(a[1]);
                        DateTime dtEnd = DateTime.Parse(a[2]);
                        tsTranslation = dtTranslation - dtStart;
                        tsPRP = dtEnd - dtTranslation;
                        tsTotal = dtEnd - dtStart;
                    }
                }
                using (StreamWriter sw = new StreamWriter(sPath + "/poprp.results.txt", true))
                {
                    sw.Write(dSub.Name);
                    sw.Write("," + bValid + "," + cNodes);
                    sw.Write("," + tsTranslation.TotalSeconds + "," + tsPRP.TotalSeconds + "," + tsTotal.TotalSeconds);
                    sw.WriteLine();
                }
            }
        }





        static void RunPlanner(string sPath, bool bOnline, DeadendStrategy ds, int iTimePerProblem)
        {

            RunPlanner(sPath + "d.pddl", sPath + "p.pddl", sPath + "dead.pddl", sPath, bOnline, ds, iTimePerProblem);

        }



        static void RunPlanner(string sDomainFile, string sProblemFile, string sDeadendFile, string sOutputPath, bool bOnline, DeadendStrategy ds, int iTimePerProblem)
        {

            Debug.WriteLine("Reading domain and problem");
            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sDomainFile);
            Problem problem = parser.ParseProblem(sProblemFile, sDeadendFile, domain);
            Debug.WriteLine("Done reading domain and problem");

            SDRPlanner.TagsCount = 2;
            SDRPlanner sdr = new SDRPlanner(sOutputPath, sDeadendFile, domain, problem, bOnline, ds);

            sdr.Start();

        }


        static void RunPlanner(string sDomainFile, string sProblemFile, string sOutputPath, bool bOnline, int iTimePerProblem)
        {

            Debug.WriteLine("Reading domain and problem");
            Parser parser = new Parser();
            Domain domain = parser.ParseDomain(sDomainFile);
            Problem problem = parser.ParseProblem(sProblemFile, domain);
            Debug.WriteLine("Done reading domain and problem");

            SDRPlanner.TagsCount = 2;
            SDRPlanner sdr = new SDRPlanner(sOutputPath, domain, problem, bOnline);

            sdr.Start();

        }

        static void MainForMultipleExperiments(string[] args)
        {
            Debug.Listeners.Add(new TextWriterTraceListener(Console.Out));
            Debug.Listeners.Add(new TextWriterTraceListener(new StreamWriter("debug.log")));
            SDRPlanner.TagsCount = 2;


            SDRPlanner.SDR_OBS = false;


            string sBenchmarkPath = BASE_PATH + @"Domains/";
            Path = BASE_PATH + @"\PDDL\";

            TestAllDeadend(@"C:\Users\shanigu\OneDrive - Ben Gurion University of the Negev\Research\projects\SDR.1\DeadEnds\Domains\", 25, false, "wood");

            Console.WriteLine("Done, press enter to exit");
            Console.ReadLine();
        }


        static void Main(string[] args)
        {
            //RunPlanner(@"C:\Users\shanigu\OneDrive - Ben Gurion University of the Negev\Research\projects\SDR.1\Domains\wumpus05\", true, DeadendStrategy.Lazy, 200);
            RunPlanner(@"C:\Users\shanigu\OneDrive - Ben Gurion University of the Negev\Research\projects\SDR.1\Offline\CLG_benchmarks\doors5\d.pddl",
                @"C:\Users\shanigu\OneDrive - Ben Gurion University of the Negev\Research\projects\SDR.1\Offline\CLG_benchmarks\doors5\p.pddl",
                @"C:\Users\shanigu\OneDrive - Ben Gurion University of the Negev\Research\projects\SDR.1\Offline\CLG_benchmarks\doors5\",
                false, 200);
        }
    }
}

