using CPORLib.LogicalUtilities;
using CPORLib.Parsing;
using CPORLib.PlanningModel;
using CPORLib.Tools;
using Python.Runtime;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;


using static CPORLib.Tools.Options;
using Action = CPORLib.PlanningModel.PlanningAction;
using Domain = CPORLib.PlanningModel.Domain;

namespace CPORLib.Algorithms
{
    public class CPORPlanner : PlannerBase
    {

        public CPORPlanner(Domain domain, Problem problem) : base(domain, problem)  
        {
            Options.ComputeCompletePlanTree = true;
        }


        //public static TextWriterTraceListener TraceListener = new TextWriterTraceListener("debug2.log");
        public static TextWriterTraceListener TraceListener = new TextWriterTraceListener();

        public ConditionalPlanTreeNode OfflinePlanning()
        {
            try
            {

                //if (Verbose)
                Console.WriteLine("Started offline planning for " + Domain.Name + ", " + DateTime.Now);

                Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> dAlreadyVisitedStates = new Dictionary<PartiallySpecifiedState, PartiallySpecifiedState>(new PartiallySpecifiedState_IEqualityComparer());
                DateTime dtStart = DateTime.Now;
                BeliefState bsInitial = Problem.GetInitialBelief();
                CPORStack<PartiallySpecifiedState> stateStack = new CPORStack<PartiallySpecifiedState>();
                int cActions = 0;
                int cPlanning = 0;
                List<PartiallySpecifiedState> lClosedStates = new List<PartiallySpecifiedState>();
                State sChosen = null;
                bool bGoalReached = false;
                bool bDone = false;
                PartiallySpecifiedState pssInitial = bsInitial.GetPartiallySpecifiedState();
                int cGoalReached = 0;




                pssInitial.mayChanged = new HashSet<Predicate>();
                pssInitial.ActionsWithConditionalEffect = new HashSet<Action>();

                stateStack.Push(pssInitial);
                PartiallySpecifiedState pssCurrent = null;
                List<List<string>> lExecutedPlans = new List<List<string>>();
                List<PartiallySpecifiedState> lGoalStates = new List<PartiallySpecifiedState>();

                Formula fObserved = null;

                bool bPreconditionFailure = false;



                while (!bDone)
                {
                    //if (cPlanning == 3)
                    //   return null;




                    bool bStateHandled = false;
                    pssCurrent = GetNextState(stateStack, lClosedStates, dAlreadyVisitedStates, out bDone, out bStateHandled);

                    if (bDone)
                        break;

                    if (bStateHandled)
                        continue;

                    if (StuckInLoopPlanBased(cActions, pssCurrent, lExecutedPlans))
                    {
                        TagsCount++;
                    }
                    else
                    {
                        if (TagsCount > 2)
                            TagsCount--;
                    }


                    if (InfoLevel > 1)
                        Console.WriteLine("Planning for state: " + pssCurrent);


                    List<string> lPlan = Plan(pssCurrent, stateStack, lClosedStates, dAlreadyVisitedStates, bPreconditionFailure, ref cPlanning, out sChosen, out bDone);

                    if (InfoLevel == 1)
                        if (lExecutedPlans.Count % 5 == 0)
                            Console.Write("\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b\b" +
                                "Replanning: " + lExecutedPlans.Count + ", goal leaves: " + cGoalReached + " closed states: " + lClosedStates.Count
                                );

                    if (bDone)
                        break;

                    PartiallySpecifiedState pssPlanState = pssCurrent;


                    if (lPlan != null)
                    {
                        if (InfoLevel > 1)
                        {
                            Console.Write("Plan: ");
                            foreach (string s in lPlan)
                                Console.Write(s + ",");
                            Console.WriteLine();
                        }

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

                                    pssCurrent.UpdateClosedStates(lClosedStates, dAlreadyVisitedStates, Domain);

                                    pssCurrent = null;
                                    break;
                                }


                                if (pssCurrent.AlreadyVisited(dAlreadyVisitedStates))
                                {
                                    PartiallySpecifiedState psIdentical = dAlreadyVisitedStates[pssCurrent];
                                    psIdentical.UpdateClosedStates(lClosedStates, dAlreadyVisitedStates, Domain);

                                    pssCurrent = null;
                                    break;
                                }


                                if (InfoLevel > 1)
                                    Console.WriteLine("Executing: " + sAction);

                                pssCurrent.ApplyOffline(sAction, out a, out bPreconditionFailure, out fObserved, out psTrueState, out psFalseState);


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
                                    pssCurrent.MarkVisited(dAlreadyVisitedStates);

                                    if (psFalseState != null && psTrueState != null)
                                    {
                                        //set the next state to be the one that the plan preferred
                                        int spaceIndex = sAction.IndexOf(' ');
                                        if (spaceIndex == -1)
                                            spaceIndex = sAction.IndexOf(Utilities.DELIMITER_CHAR);
                                        if (spaceIndex == -1)
                                            spaceIndex = sAction.Length;
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
                                    cGoalReached++;
                                    if (InfoLevel > 1)
                                        Console.WriteLine("Goal reached " + pssCurrent + " = " + Problem.Goal);

                                    pssCurrent.UpdateClosedStates(lClosedStates, dAlreadyVisitedStates, Domain);


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
                            if (pssCurrent.IsDeadEndState() == Options.DeadEndExistence.DeadEndTrue)
                                Debug.WriteLine("*");
                            if (pssCurrent.IsGoalState())
                                Debug.WriteLine("*");
                            if (InfoLevel > 1)
                                Console.WriteLine("No plan was found!!");
                        }
                    }

                }


                DateTime dtEnd = DateTime.Now;
                ExecutionData.Time = dtEnd - dtStart;
                ExecutionData.Actions = cActions;
                ExecutionData.Planning = cPlanning;

                if (InfoLevel > 0)
                {
                    Console.WriteLine();
                    Console.WriteLine(Domain.Name + " done planning, time " + (dtEnd - dtStart).TotalSeconds);
                    Console.WriteLine("----------------------------------------------------------------------------------------------");
                }

                CPORPlanner.TraceListener.Write("Success " + pssInitial.Plan);
                //WritePlan("plan.txt", pssInitial.Plan);
                TraceListener.Flush();
                TraceListener.Close();

                return pssInitial.Plan;
            }
            catch(Exception e)
            {
                Console.WriteLine("Caught an exception: " + e.Message);
                Console.WriteLine(e.StackTrace);


                CPORPlanner.TraceListener.Write(e.StackTrace);
                TraceListener.Flush();
                TraceListener.Close();
                return null;
            }

        }






        public static bool ValidatePlanGraph(string sPlanFile, Domain d, Problem p, out int cNodes)
        {
            bool bComputePlanTree = Options.ComputeCompletePlanTree;
            Options.ComputeCompletePlanTree = true;
            ConditionalPlanTreeNode nRoot = ReadPlan(sPlanFile, d);

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
            bool bValid = ValidatePlanGraph(pssInit, nRoot, new List<ConditionalPlanTreeNode>(), new List<string>(), DateTime.Now, new TimeSpan(0, 15, 0), ref cLeaves);
            Options.ComputeCompletePlanTree = bComputePlanTree;
            return bValid;
        }

        public bool ValidatePlanGraph(ConditionalPlanTreeNode nCurrent)
        {
            int cCheckedLeaves = 0;
            return ValidatePlanGraph(Problem.GetInitialBelief().GetPartiallySpecifiedState(), nCurrent, new List<ConditionalPlanTreeNode>(), new List<string>(), DateTime.Now, new TimeSpan(0, 15, 0), ref cCheckedLeaves);
        }

        public static bool ValidatePlanGraph(PartiallySpecifiedState pssCurrent, ConditionalPlanTreeNode nCurrent, List<ConditionalPlanTreeNode> lHistory, List<string> ll,
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
                if (pssCurrent.IsDeadEndState() == Options.DeadEndExistence.DeadEndTrue)
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
                return ValidatePlanGraph(psTrueState, nCurrent.SingleChild, lHistory, ll, dtStart, tsMax, ref cCheckedLeaves);
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
                bTrueOk = ValidatePlanGraph(psTrueState, nCurrent.TrueObservationChild, lTrueHistory, x1, dtStart, tsMax, ref cCheckedLeaves);
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
                bFalseOk = ValidatePlanGraph(psFalseState, nCurrent.FalseObservationChild, lFalseHistory, x2, dtStart, tsMax, ref cCheckedLeaves);
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
                    string[] aLine = Utilities.SplitString(sLine, ' ' , StringSplitOptions.RemoveEmptyEntries);
                    int idx1 = int.Parse(aLine[0]);
                    int idx2 = int.Parse(aLine[1]);
                    if (!dEdges.ContainsKey(idx1))
                        dEdges[idx1] = new HashSet<int>();
                    dEdges[idx1].Add(idx2);
                }
                else //node
                {
                    string[] aLine = Utilities.SplitString(sLine, new char[] { '[', '\"' });
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
                            Action a = d.GroundActionByName(Utilities.SplitString(sAction,' ' ));
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


        public void WritePlan(string sPlanFile, ConditionalPlanTreeNode nInitial)
        {
            WritePlan(sPlanFile, Problem.GetInitialBelief().GetPartiallySpecifiedState(), nInitial);
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

            if (pssCurrent.IsDeadEndState() == Options.DeadEndExistence.DeadEndTrue)
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

        public PartiallySpecifiedState GetNextState(CPORStack<PartiallySpecifiedState> stateStack, List<PartiallySpecifiedState> lClosedStates, 
            Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> dAlreadyVisitedStates, out bool bDone, out bool bStateHandled)
        {
            bDone = false;
            bStateHandled = false;
            if (stateStack.Count == 0)
            {
                bDone = true;
                return null;
            }
            PartiallySpecifiedState pssCurrent = stateStack.Pop(); ;
            if (pssCurrent.IsClosedState(lClosedStates))
            {
                //Debug.WriteLine("Found closed state");
                pssCurrent.UpdateClosedStates(lClosedStates, dAlreadyVisitedStates, Domain);
                
                if (stateStack.Count == 0)
                {
                    bDone = true;
                }
                bStateHandled = true;
            }
            else if (pssCurrent.AlreadyVisited(dAlreadyVisitedStates))
            {
                PartiallySpecifiedState psIdentical = dAlreadyVisitedStates[pssCurrent];
                pssCurrent.UpdateClosedStates(lClosedStates, dAlreadyVisitedStates, Domain);
                
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
                    List<Action> lObservationActions =Domain.GroundAllObservationActions(pssCurrent.Observed, true);
                    foreach (Action a in lObservationActions)
                    {
                        Predicate pObserve = ((PredicateFormula)a.Observe).Predicate;
                        if (!pssCurrent.Observed.Contains(pObserve) && !pssCurrent.Observed.Contains(pObserve.Negate()))
                        {
                            Formula fObserved = null;
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
            return pssCurrent;
        }


        public List<string> Plan(PartiallySpecifiedState pssCurrent, CPORStack<PartiallySpecifiedState> stateStack, List<PartiallySpecifiedState> lClosedStates,
            Dictionary<PartiallySpecifiedState, PartiallySpecifiedState> dAlreadyVisitedStates, bool bPreconditionFailure, ref int cPlanning, out State sChosen, out bool bDone)
        {
            List<string> lPlan = null;
            bool bDeadendClosed = false;
            bool bMaybeDeadend = false;
            sChosen = null;
            bDone = false;

            /*
            //BUGBUG: only for debugging localize 5
            lPlan = new List<string>();
            lPlan.Add("checking");
            lPlan.Add("sense-riFF.Search.gHt-t");
            lPlan.Add("sense-left-t");
            lPlan.Add("move-riFF.Search.gHt");
            lPlan.Add("checking");
            lPlan.Add("sense-riFF.Search.gHt-t");
            lPlan.Add("move-riFF.Search.gHt");
            return lPlan;
            */






            while (lPlan == null || lPlan.Count == 0)
            {
                
                DateTime dtBefore = DateTime.Now;
                cPlanning++;
                lPlan = null;


                if (lPlan == null)
                {

                    if (DeadendStrategy == DeadendStrategies.Classical)
                    {
                        bool bIsDeadEnd = false;
                        lPlan = PlanWithClassicalDeadendDetection(pssCurrent, out sChosen, out bIsDeadEnd);
                        if (bIsDeadEnd)
                        {
                            HashSet<Predicate> hsDeadend = new HashSet<Predicate>();
                            hsDeadend.Add(Utilities.FALSE_PREDICATE);
                            pssCurrent.UpdateClosedStates(lClosedStates, dAlreadyVisitedStates, Domain, hsDeadend);
                            if (stateStack.Count == 0)
                            {
                                bDone = true;
                                break;
                            }
                            bDeadendClosed = true;
                            pssCurrent = stateStack.Pop();
                            continue;
                        }
                    }
                    else
                    {
                        bMaybeDeadend = false;
                        bDeadendClosed = false;

                        List<Formula> lDeadends = null;
                        //Debug.WriteLine(pssCurrent);
                        DeadEndExistence isDeadEnd = pssCurrent.IsDeadEndExistenceAll(out lDeadends);
                        if (isDeadEnd == DeadEndExistence.MaybeDeadEnd)
                        {
                            
                                bMaybeDeadend = true;
                                
                                lPlan = PlanToObserveDeadEnd(pssCurrent, lDeadends, bPreconditionFailure, out sChosen);
                                break;
                            
                        }
                        else if (isDeadEnd == DeadEndExistence.DeadEndTrue)
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

                            pssCurrent.UpdateClosedStates(lClosedStates, dAlreadyVisitedStates, Domain, deadList);
                            if (stateStack.Count == 0)
                            {
                                bDone = true;
                                break;
                            }

                            bDeadendClosed = true;

                        }




                        if (bMaybeDeadend == false && bDeadendClosed)
                        {
                            pssCurrent = stateStack.Pop();
                            continue;

                        }




                        if (lPlan == null && bMaybeDeadend == false && bDeadendClosed == false)
                        {
                            lPlan = base.Plan(pssCurrent, out sChosen);
                        }
                    }
                }

                if (lPlan == null)
                {
                    throw new Exception("Failed to plan for current state");
                }
            }
            return lPlan;

        }
    }
}
