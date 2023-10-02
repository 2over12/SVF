#include "SABER/UseAfterFreeChecker.h"
#include "Graphs/ICFGNode.h"
#include "Graphs/SVFG.h"
#include "Graphs/VFGNode.h"
#include "SABER/LeakChecker.h"
#include "SVFIR/SVFStatements.h"
#include "SVFIR/SVFType.h"
#include "Util/Casting.h"
#include "Util/DPItem.h"
#include "Util/GraphReachSolver.h"
#include "Util/SVFBugReport.h"
#include <unordered_set>
#include <vector>

using namespace SVF;
using namespace SVFUtil;

namespace
{
class ICFGReachabilityAnalysis : GraphReachSolver<ICFG*, CxtDPItem>
{

private:
    const ICFG* graph;
    const ICFGNode* src;
    std::unordered_set<const ICFGNode*> nodeset;

protected:
    virtual void FWProcessCurNode(const CxtDPItem& it)
    {
        nodeset.insert(graph->getICFGNode(it.getCurNodeID()));
    }

public:
    ICFGReachabilityAnalysis(ICFG* graph, const ICFGNode* src)
        : graph(graph), src(src)
    {
        this->setGraph(graph);
    }

    const std::unordered_set<const ICFGNode*> getNodeSet()
    {
        return nodeset;
    }

    void analyze()
    {

        ContextCond ctx;
        CxtDPItem it(src->getId(), ctx);
        forwardTraverse(it);
    }
};
} // namespace

void UseAfterFreeChecker::initSnks()
{
    LeakChecker::initSnks();

    for (auto s : this->getSinks())
    {

        this->frees.insert(s);
    }

    auto cg = getSVFG();

    for (auto it = cg->begin(); it != cg->end(); it++)
    {
        auto nd = it->second;
        if (isa<LoadVFGNode>(nd) || isa<StoreVFGNode>(nd))
        {
            auto st = cast<StmtVFGNode>(nd);

            auto target_pointer = cg->getDefSVFGNode(st->getPAGSrcNode());
            if (isa<StoreSVFGNode>(nd))
            {
                target_pointer = cg->getDefSVFGNode(st->getPAGDstNode());
            }

            pointer_to_use.insert({target_pointer, st});
            addToSinks(target_pointer);
        }
    }
}

/// Report file/close bugs
void UseAfterFreeChecker::reportBug(ProgSlice* slice)
{
    auto ir = getPAG();
    auto icfg = ir->getICFG();
    // for every free, and every
    // and every use that can alias check if the use is reachable
    // from the free
    std::vector<const StmtSVFGNode*> uses;
    for (auto maybe_use : slice->getSinks())
    {
        auto it_and_end = this->pointer_to_use.equal_range(maybe_use);
        for (auto it = it_and_end.first; it != it_and_end.second; it++)
        {
            uses.push_back(it->second);
        }
    }

    for (auto maybe_free : slice->getSinks())
    {

        if (this->frees.find(maybe_free) != this->frees.end())
        {

            ICFGReachabilityAnalysis reach(icfg, maybe_free->getICFGNode());
            reach.analyze();
            for (auto use : uses)
            {
                auto dst_node = use->getICFGNode();
                if (reach.getNodeSet().find(dst_node) !=
                    reach.getNodeSet().end())
                {
                    GenericBug::EventStack eventStack;
                    eventStack.push_back(
                        SVFBugEvent(SVFBugEvent::SourceInst, use->getInst()));

                    report.addSaberBug(GenericBug::BugType::USEAFTEFREE,
                                       eventStack);
                }
            }
        }
    }
}
