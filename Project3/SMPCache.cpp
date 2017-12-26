/*
   SESC: Super ESCalar simulator
   Copyright (C) 2003 University of Illinois.

   Contributed by Karin Strauss

This file is part of SESC.

SESC is free software; you can redistribute it and/or modify it under the terms
of the GNU General Public License as published by the Free Software Foundation;
either version 2, or (at your option) any later version.

SESC is    distributed in the  hope that  it will  be  useful, but  WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU General Public License for more details.

You should  have received a copy of  the GNU General  Public License along with
SESC; see the file COPYING.  If not, write to the  Free Software Foundation, 59
Temple Place - Suite 330, Boston, MA 02111-1307, USA.
*/

#include "SMPCache.h"
#include "SMPCacheState.h"
#include "libmem/Cache.h"

#include "MESIProtocol.h"
#include "DMESIProtocol.h"

#include "SMPSliceCache.h"

#include "SMPRouter.h"

#include <iomanip>

#if (defined DEBUG_LEAK)
Time_t Directory::lastClock = 0;
uint64_t Directory::totCnt = 0;
#endif
//bool SMPCache::msgPrinted = false;
#if (defined DLCHECK)
unsigned int Cache::dlcnt = 0;
#endif

#if (defined CHECK_STALL)
extern unsigned long long lastFin;
#endif

//std::set<SMPMemRequest*> SMPCache::detourSet;
//std::map<SMPMemRequest*, SMPMemRequest*> SMPCache::replaceMap;
//#define DEBUGPRINT printf
extern char* MemOperationStr[];

SMPMemRequest::MESHSTRMAP SMPMemRequest::SMPMemReqStrMap;

const char* SMPCache::cohOutfile = NULL;
	
// This cache works under the assumption that caches above it in the memory
// hierarchy are write-through caches

// There is a major simplifying assumption for this cache subsystem:
// if there are two requests to the same cache line at the same time,
// only one of them is propagated to the lower levels. Once this
// request is serviced, the other one will be allowed to proceed. This
// is implemented by the mutExclBuffer.

// When this cache is not used as the last level of caching before
// memory, we are assuming all levels between this cache and memory
// are not necessarily inclusive. This does not mean they are
// exclusive.

// Another important assumption is that every cache line in the memory
// subsystem is the same size. This is not hard to fix, though. Any
// candidates?

//MSHR<PAddr, SMPCache> *SMPCache::mutExclBuffer = NULL;
//std::map<PAddr, MemRequest* > SMPCache::mutInvReq;
//HASH_MAP<PAddr, std::list<CallbackBase*> > SMPCache::pendingList;

#ifdef SESC_ENERGY
unsigned SMPCache::cacheID = 0;
#endif

SMPCache::SMPCache(SMemorySystem *dms, const char *section, const char *name)
    : MemObj(section, name)
    , readHit("%s:readHit", name)
    , writeHit("%s:writeHit", name)
    , readMiss("%s:readMiss", name)
    , writeMiss("%s:writeMiss", name)
    , readHalfMiss("%s:readHalfMiss", name)
    , writeHalfMiss("%s:writeHalfMiss", name)
    , writeBack("%s:writeBack", name)
    , linePush("%s:linePush", name)
    , lineFill("%s:lineFill", name)
    , readRetry("%s:readRetry", name)
    , writeRetry("%s:writeRetry", name)
    , invalDirty("%s:invalDirty", name)
    , allocDirty("%s:allocDirty", name)
    , rcompMiss("%s:rcompMiss", name)
    , wcompMiss("%s:wcompMiss", name)
    , rreplMiss("%s:rreplMiss", name)
    , wreplMiss("%s:wreplMiss", name)
    , rcoheMiss("%s:rcoheMiss", name)
    , wcoheMiss("%s:wcoheMiss", name)

{
    MemObj *lowerLevel = NULL;
    //printf("%d\n", dms->getPID());
    cacheHelper = new CacheHelper(name);
    listofInvalidTags=new std::set<uint>();
    I(dms);
    lowerLevel = dms->declareMemoryObj(section, "lowerLevel");

    MemObj *sideLowerLevel = NULL;
    const char *sLL = SescConf->getCharPtr(section, "sideLowerLevel");
    bool bLL = (strlen(sLL) > 0);
    //printf("bool : %d\n", bLL);
    dataCache = bLL;
    if(bLL) {
        sideLowerLevel = dms->declareMemoryObj(section, "sideLowerLevel");
        if(sideLowerLevel != NULL) {
            addSideLowerLevel(sideLowerLevel);
        }
    }

    if (lowerLevel != NULL) {
        addLowerLevel(lowerLevel);
        // JJO
#if 0
        // is this IL1 or DL1?
        for(uint32_t i=0; i<lowerLevel->getUpperLevelSize(); i++) {
            if((*(lowerLevel->getUpperLevel()))[i]==this) {
                levelIdx = i;
                //printf("%s %d\n", getSymbolicName(), i);
                break;
            }
        }
#endif
    }

    cache = CacheType::create(section, "", name);
    I(cache);

    const char *prot = SescConf->getCharPtr(section, "protocol");
    if(!strcasecmp(prot, "MESI")) {
        //protocol = new MESIProtocol(this, name);
        IJ(0);
    }
    // JJO begin
    else if (!strcasecmp(prot, "DMESI")) {
        protocol = new DMESIProtocol(this, name);
    } else {
        MSG("unknown protocol, using MESI");
        IJ(0);
        //protocol = new MESIProtocol(this, name);
    }

    SescConf->isInt(section, "numPorts");
    SescConf->isInt(section, "portOccp");

    cachePort = PortGeneric::create(name,
                                    SescConf->getInt(section, "numPorts"),
                                    SescConf->getInt(section, "portOccp"));

    // JJO
    nodeID = dms->getPID();
    maxNodeID = dms->getPPN();
	maxNodeID_bit = log2i(maxNodeID);
    //printf("%s nID: %d / %d\n",name, nodeID, maxNodeID);
	nodeSelSht = 0;
	if(SescConf->checkInt(section, "nodeSel")) {
		nodeSelSht = SescConf->getInt(section, "nodeSel");
	}
   
	if(SescConf->checkCharPtr(section, "cohOutput")) {
		const char *coh_out = SescConf->getCharPtr(section, "cohOutput");
		//printf("coh %s\n", SMPCache::cohOutfile);
		if(SMPCache::cohOutfile == NULL) {
			SMPCache::cohOutfile = coh_out;
		}
	}

    // MSHR is used as an outstanding request buffer
    // even hits are added to MSHR
    char *outsReqName = (char *) malloc(strlen(name) + 2);
    sprintf(outsReqName, "%s", name);

    const char *mshrSection = SescConf->getCharPtr(section,"MSHR");

    outsReq = MSHR<PAddr,SMPCache>::create(outsReqName, mshrSection);

#if 0
    if (mutExclBuffer == NULL)
        mutExclBuffer = MSHR<PAddr,SMPCache>::create("mutExclBuffer",
                        SescConf->getCharPtr(mshrSection, "type"),
                        32000,
                        SescConf->getInt(mshrSection, "bsize"));
#endif

    SescConf->isInt(section, "hitDelay");
    hitDelay = SescConf->getInt(section, "hitDelay");

    SescConf->isInt(section, "missDelay");
    missDelay = SescConf->getInt(section, "missDelay");

#ifdef SESC_ENERGY

    myID = cacheID;
    cacheID++;

    rdEnergy[0] = new GStatsEnergy("rdHitEnergy",name
                                   ,myID
                                   ,MemPower
                                   ,EnergyMgr::get(section,"rdHitEnergy"));

    rdEnergy[1] = new GStatsEnergy("rdMissEnergy",name
                                   ,myID
                                   ,MemPower
                                   ,EnergyMgr::get(section,"rdMissEnergy"));

    wrEnergy[0]  = new GStatsEnergy("wrHitEnergy",name
                                    ,myID
                                    ,MemPower
                                    ,EnergyMgr::get(section,"wrHitEnergy"));

    wrEnergy[1] = new GStatsEnergy("wrMissEnergy",name
                                   ,myID
                                   ,MemPower
                                   ,EnergyMgr::get(section,"wrMissEnergy"));
#endif
    if(SMPMemRequest::SMPMemReqStrMap.empty()) {
        SMPMemRequest::SMPMemReqStrMap[ReadRequest]= 		   "ReadRequest";
        SMPMemRequest::SMPMemReqStrMap[ExclusiveReply]=		   "ExclusiveReply";
        //SMPMemRequest::SMPMemReqStrMap[ForwardRequest]=		   "ForwardRequest";
        //SMPMemRequest::SMPMemReqStrMap[ForwardRequestNAK]=		   "ForwardRequestNAK";
        SMPMemRequest::SMPMemReqStrMap[IntervSharedRequest]=	   "IntervSharedRequest";
        SMPMemRequest::SMPMemReqStrMap[SpeculativeReply]=	   "SpeculativeReply";
        SMPMemRequest::SMPMemReqStrMap[SharedReply]=			   "SharedReply";
        SMPMemRequest::SMPMemReqStrMap[SharedResponse]=		   "SharedResponse";
        SMPMemRequest::SMPMemReqStrMap[SharingWriteBack]=		   "SharingWriteBack";
        SMPMemRequest::SMPMemReqStrMap[SharedAck]=			   "SharedAck";
        SMPMemRequest::SMPMemReqStrMap[SharingTransfer]=		   "SharingTransfer";
        SMPMemRequest::SMPMemReqStrMap[WriteRequest]=		   "WriteRequest";
        SMPMemRequest::SMPMemReqStrMap[Invalidation]=		   "Invalidation";
        SMPMemRequest::SMPMemReqStrMap[InvalidationAck]=		   "InvalidationAck";
        //SMPMemRequest::SMPMemReqStrMap[InvalidationAckData]=	   "InvalidationAckData";
        SMPMemRequest::SMPMemReqStrMap[ExclusiveReplyInv]=	   "ExclusiveReplyInv";
        SMPMemRequest::SMPMemReqStrMap[IntervExRequest]=		   "IntervExRequest";
        SMPMemRequest::SMPMemReqStrMap[ExclusiveResponse]=	   "ExclusiveResponse";
        SMPMemRequest::SMPMemReqStrMap[DirtyTransfer]=		   "DirtyTransfer";
        SMPMemRequest::SMPMemReqStrMap[ExclusiveAck]=		   "ExclusiveAck";
        SMPMemRequest::SMPMemReqStrMap[UpgradeRequest]=		   "UpgradeRequest";
        SMPMemRequest::SMPMemReqStrMap[ExclusiveReplyInvND]=		   "ExclusiveReplyInvND";
        SMPMemRequest::SMPMemReqStrMap[WriteBackRequest]=	   "WriteBackRequest";
        SMPMemRequest::SMPMemReqStrMap[TokenBackRequest]=	   "TokenBackRequest";
        SMPMemRequest::SMPMemReqStrMap[WriteBackExAck]=		   "WriteBackExAck";
        SMPMemRequest::SMPMemReqStrMap[WriteBackBusyAck]=	   "WriteBackBusyAck";
        //SMPMemRequest::SMPMemReqStrMap[SharedResponseDummy]=	   "SharedResponseDummy";
        //SMPMemRequest::SMPMemReqStrMap[ExclusiveResponseDummy]= "ExclusiveResponseDummy";
        //SMPMemRequest::SMPMemReqStrMap[WriteBackRequestData]=   "WriteBackRequestData";
        SMPMemRequest::SMPMemReqStrMap[NAK]=				   "NAK";
        SMPMemRequest::SMPMemReqStrMap[MeshMemPush]=		   "MeshMemPush";
        SMPMemRequest::SMPMemReqStrMap[MeshMemAccess]=		   "MeshMemAccess";
        SMPMemRequest::SMPMemReqStrMap[MeshMemAccessReply]=   "MeshMemAccessReply";
        //SMPMemRequest::SMPMemReqStrMap[MeshMemWriteBack]=	   "MeshMemWriteBack";
        SMPMemRequest::SMPMemReqStrMap[NOP]=				   "NOP";
    }
}

void SMPCache::PrintStat()
{
	std::ostream* out = &cout;
	std::ofstream cohOut;
	if(cohOutfile!=NULL) {
		cohOut.open(cohOutfile, ios::out|ios::trunc);
		out = &cohOut;
	}

	(*out)<<std::endl;
	(*out)<<std::endl;
	(*out)<<"======================= Coherence message stat ======================";
	(*out)<<std::endl;
	(*out)<<std::endl;
	for(SMPMemRequest::MESHSTRMAP::iterator it = SMPMemRequest::SMPMemReqStrMap.begin();
			it!=SMPMemRequest::SMPMemReqStrMap.end(); it++) {
		(*out)<<"\t"<<std::left<<std::setw(30)<<(*it).second<<"\t"<<std::right<<SMPMemRequest::nSMPMsg[(*it).first];
		(*out)<<std::endl;
	}

	(*out)<<std::endl;
	(*out)<<std::endl;
	(*out)<<std::endl;
	(*out)<<std::endl;
	(*out)<<"======================= Network selection stat ======================";
	(*out)<<std::endl;
	(*out)<<std::endl;
	(*out)<<"\tSIZE         : "<<SMPRouter::sizeStat<<std::endl;
	(*out)<<std::endl;
	(*out)<<std::endl;
	(*out)<<"======================= Message per Network selection stat ======================\n\n";
	for(SMPMemRequest::MESHSTRMAP::iterator it = SMPMemRequest::SMPMemReqStrMap.begin();
			it!=SMPMemRequest::SMPMemReqStrMap.end(); it++) {
		(*out)<<"\t"<<std::left<<std::setw(30)<<(*it).second<<std::right<<"\t"<<SMPRouter::msgStat[(*it).first];
		(*out)<<std::endl;
	}
	(*out)<<std::endl;
	(*out)<<std::endl;
	(*out)<<"\tMultipleDestInvalidation : "<<SMPRouter::mdestStat;
	(*out)<<std::endl;
	(*out)<<"\tTotDestInvalidation : "<<SMPRouter::mtotDestStat;
	(*out)<<std::endl;
	(*out)<<std::endl;
	(*out)<<std::endl;

	if(cohOutfile!=NULL) {
		cohOut.close();
	}
}

SMPCache::~SMPCache()
{
    // do nothing
}

Time_t SMPCache::getNextFreeCycle() const
{
    return cachePort->calcNextSlot();
}

bool SMPCache::canAcceptStore(PAddr addr)
{
    return outsReq->canAcceptRequest(addr);
}

void SMPCache::access(MemRequest *mreq)
{
    PAddr addr;
    IS(addr = mreq->getPAddr());

    GMSG(mreq->getPAddr() < 1024,
         "mreq dinst=0x%p paddr=0x%x vaddr=0x%x memOp=%d ignored",
         mreq->getDInst(),
         (uint32_t) mreq->getPAddr(),
         (uint32_t) mreq->getVaddr(),
         mreq->getMemOperation());

    I(addr >= 1024);

    //addr = mreq->getPAddr();
	//
	//if(globalClock>72000000 && globalClock<72500000) sdprint=true;
	//if(globalClock>72500000) sdprint=false;
	
	//if(globalClock>1860071) sdprint=true;

    //if(globalClock>136610811) sdprint = true;	// req: ocean
    //if(globalClock>245135536) sdprint = true;  // req: water-nsq
    //if(globalClock>24460263) sdprint = true; // adapt: ocean

    //if(globalClock>194430698) sdprint = true; // adapt: lu-cn
    //if(globalClock>13528155) sdprint = true; // adapt: ocean-nc
    //if(globalClock>97830789) sdprint = true; // adapt: ocean
    //if(globalClock>32780027) sdprint = true; // adapt: barnes
    //if(globalClock>34050661) sdprint = true; // adapt: water-sp
    //if(globalClock>19470786) sdprint = true; // adapt: ocean-nc

    //if(globalClock>66719385) sdprint = true; // conj : ocean
    //if(globalClock>18290773) sdprint = true; // conj : radiosity
    //if(globalClock>17310761) sdprint = true; // req : ocean
    //if(globalClock>22710649) sdprint = true; // req : radiosity

    //if(globalClock>=158215945) sdprint = true;
    //if(globalClock>=158250945) exit(1);
    //if(globalClock>=308702606) sdprint = true;
    //if(globalClock>=309762606) exit(1);

    //if(globalClock>26195458) sdprint = true; // conj: ocean
    //if(globalClock>15059061) sdprint = true; // conj: ocean
    //if(globalClock>64640989) sdprint = true; // adapt: ocean
    //if(globalClock>15063777) sdprint = true; // adapt: ocean
    //if(globalClock>24958833) sdprint = true; // adapt: ocean

    //if(globalClock>7471010) sdprint = true; // adapt: ocean

    //if(globalClock>16259059229) sdprint = true; // 100p: facesim

    //if(globalClock>130660443) sdprint = true; // conj:ocean 130670443
    //sdprint = true;

    switch(mreq->getMemOperation()) {
    case MemRead:
        read(mreq);
        break;
    case MemWrite: /*I(cache->findLine(mreq->getPAddr())); will be transformed
						 to MemReadW later */
    case MemReadW:
        write(mreq);
        break;
    case MemPush:
        I(0);
        break; // assumed write-through upperlevel
    default:
        specialOp(mreq);
        break;
    }

    // for reqs coming from upper level:
    // MemRead  means "I want to read"
    // MemReadW means "I want to write, and I missed"
    // MemWrite means "I want to write, and I hit"
    // MemPush  means "I am writing data back"
    // (this will never happen if upper level is write-through cache,
    // which is what we are assuming)
}

void SMPCache::read(MemRequest *mreq)
{
    PAddr addr = mreq->getPAddr();
    //if(calcTag(addr)==0x1edfd4e) sdprint=true;
    //if(addr==0x7e97208c) sdprint=true;
    //if(globalClock>500000) sdprint=true;
    //if(globalClock>4529885) sdprint=true;
    //sdprint = true;
    //if(globalClock>69648335 && addr==0x418c004) sdprint=true;
    //
    //
    //
    //

    if (!outsReq->issue(addr)) {
        // DEBUGPRINT("[%s] read half miss %x at %lld\n",getSymbolicName(), addr,  globalClock );
        outsReq->addEntry(addr, doReadCB::create(this, mreq),
                          doReadCB::create(this, mreq));
        readHalfMiss.inc();
        return;
    }

    doReadCB::scheduleAbs(nextSlot(), this, mreq);
}

void SMPCache::doRead(MemRequest *mreq)
{
    PAddr addr = mreq->getPAddr();
    Line *l = cache->readLine(addr);

    //std::cout << cache->calcSet4Tag(addr) << std::endl;
    if(!((l && l->canBeRead()))) {
        DEBUGPRINT("[%s] read %x miss at %lld\n",getSymbolicName(), addr,  globalClock );
    }

    //if(addr==0x7e9ee000 || addr==0x7e9ee02c) sdprint=true;
    //if(globalClock>220000000) sdprint=true;
    //sdprint = true;
    
    if (l && l->canBeRead() && l->isValid()) {
        cacheHelper -> lruStack -> updateLRUStack(calcTag(addr));
        readHit.inc();
#ifdef SESC_ENERGY
        rdEnergy[0]->inc();
#endif
        outsReq->retire(addr);
        mreq->goUp(hitDelay);
        return;
    }
    

    //std::cout << l->isValid() << std::endl;
    if (l && l->isLocked()) {
        readRetry.inc();
        //DEBUGPRINT("[%s] read locked %x miss at %lld\n",getSymbolicName(), addr,  globalClock );
        Time_t nextTry = nextSlot();
        if (nextTry == globalClock)
            nextTry++;
        doReadCB::scheduleAbs(nextTry, this, mreq);
        return;
    }

    GI(l, !l->isLocked());
    // My Code
    bool missed = false;
    if (listofInvalidTags->find(calcTag(addr))!=listofInvalidTags->end()) {
        rcoheMiss.inc();
        std::cout << "Coh" << std::endl;
        missed=true;
    } else {
        //Check for 3Cs
        if (cacheHelper -> checkCompMiss(calcTag(addr))) 
            rcompMiss.inc();
        else {
            rreplMiss.inc();
        }
    }

    

    readMiss.inc();
     //if(pendInvTable.size() == 0)
     //   capMiss.inc();
    //std::cout << pendInvTable.size() << std::endl;

#if (defined TRACK_MPKI)
    DInst *dinst = mreq->getDInst();
    if(dinst) {
        ThreadContext *context = dinst->context;
        if(context) {
            ThreadContext::nL1CM[context->getPid()]++;
        }
	}
#endif


#ifdef SESC_ENERGY
    rdEnergy[1]->inc();
#endif

#if 0
    if (!mutExclBuffer->issue(addr)) {
        //DEBUGPRINT("[%s] read issue full %x miss at %lld\n",getSymbolicName(), addr,  globalClock );
        mutExclBuffer->addEntry(addr, sendReadCB::create(this, mreq),
                                sendReadCB::create(this, mreq));
        return;
    }
#endif

    sendRead(mreq);
}

void SMPCache::sendRead(MemRequest* mreq)
{
    protocol->read(mreq);
}

void SMPCache::write(MemRequest *mreq)
{
    PAddr addr = mreq->getPAddr();

    if (!outsReq->issue(addr)) {
        outsReq->addEntry(addr, doWriteCB::create(this, mreq),
                          doWriteCB::create(this, mreq));
        writeHalfMiss.inc();
        return;
    }

    doWriteCB::scheduleAbs(nextSlot(), this, mreq);
}

void SMPCache::doWriteAgain(MemRequest *mreq) {
    PAddr addr = mreq->getPAddr();
    Line *l = cache->writeLine(addr);
    IJ(l && l->canBeWritten());
    if(l && l->canBeWritten()) {
        writeHit.inc();
#ifdef SESC_ENERGY
        wrEnergy[0]->inc();
#endif
        protocol->makeDirty(l);
        outsReq->retire(addr);
        mreq->goUp(hitDelay);
        return;
    } else {
        IJ(0);
    }
}

void SMPCache::doWrite(MemRequest *mreq)
{
    PAddr addr = mreq->getPAddr();
    Line *l = cache->writeLine(addr);

    if(!(l && l->canBeWritten())) {
        DEBUGPRINT("[%s] write %x (%x) miss at %lld [state %x]\n",
                   getSymbolicName(), addr, calcTag(addr), globalClock, (l?l->getState():-1) );
    }

    if (l && l->canBeWritten()) {
        cacheHelper -> lruStack -> updateLRUStack(calcTag(addr));
        writeHit.inc();
#ifdef SESC_ENERGY
        wrEnergy[0]->inc();
#endif
        protocol->makeDirty(l);
        outsReq->retire(addr);
        mreq->goUp(hitDelay);
        return;
    }

    if (l && l->isLocked()) {
        DEBUGPRINT(" Locked %x ... try again\n", addr);
        //printf(" Locked %x ... try again %lld\n", addr, globalClock);
        writeRetry.inc();
        mreq->mutateWriteToRead();
        Time_t nextTry = nextSlot();
        if (nextTry == globalClock)
            nextTry++;
        doWriteCB::scheduleAbs(nextTry, this, mreq);
        return;
    }

    GI(l, !l->isLocked());

    // this should never happen unless this is highest level because
    // SMPCache is inclusive of all other caches closer to the
    // processor; there is only one case in which this could happen when
    // SMPCache is used as an L2: 1) line is written in L1 and scheduled
    // to go down to L2 2) line is invalidated in both L1 and L2 3)
    // doWrite in L2 is executed after line is invalidated
    if(!l && mreq->getMemOperation() == MemWrite) {
        mreq->mutateWriteToRead();
    }

    if (listofInvalidTags->find(calcTag(addr))!=listofInvalidTags->end()) {
        wcoheMiss.inc();
        //std::cout << "Wrong" << std::endl;
    } 
    else {
        //Check for 3Cs
        if (cacheHelper -> checkCompMiss(calcTag(addr))) 
            wcompMiss.inc();
        else {
            wreplMiss.inc();
        }
    }

    writeMiss.inc();

#ifdef SESC_ENERGY
    wrEnergy[1]->inc();
#endif

#if 0
    if (!mutExclBuffer->issue(addr)) {
        mutExclBuffer->addEntry(addr, sendWriteCB::create(this, mreq),
                                sendWriteCB::create(this, mreq));
        return;
    }
#endif

    sendWrite(mreq);
}

void SMPCache::sendWrite(MemRequest* mreq)
{
    protocol->write(mreq);
}

void SMPCache::doWriteBack(PAddr addr)
{
    // FIXME: right now we are assuming cache line sizes are same in every cache

    writeBack.inc();
// protocol->sendWriteBack(addr, /*concludeWriteBackCB::create(this, globalClock)*/ NULL);
}

void SMPCache::concludeWriteBack(Time_t initialTime)
{
    // add here actions that need to be performed after writeback is
    // acknoledged by memory
}

void SMPCache::specialOp(MemRequest *mreq)
{
    mreq->goUp(1);
}

void SMPCache::invalidate(PAddr addr, ushort size, MemObj *oc)
{
    IJ(0);
#if 0
    Line *l = cache->findLine(addr);

    I(oc);
    I(pendInvTable.find(addr) == pendInvTable.end());
    pendInvTable[addr].outsResps = getNumCachesInUpperLevels();
    pendInvTable[addr].cb = doInvalidateCB::create(oc, addr, size);
    pendInvTable[addr].invalidate = true;
    //  pendInvTable[addr].writeback = true;

    if (l)
        protocol->preInvalidate(l);

    if (!isHighestLevel()) {
        IJ(0);
        invUpperLevel(addr, size, this);
        return;
    }

    doInvalidate(addr, size);
#endif
}

void SMPCache::doInvalidate(PAddr addr, ushort size)
{
    IJ(pendInvTable.find(addr) != pendInvTable.end());
    CallbackBase *cb = 0;
    bool invalidate = false;
    bool writeBack = false;

    PendInvTable::iterator it = pendInvTable.find(addr);
    Entry *record = &(it->second);
#if 0
    if(--(record->outsResps) <= 0) {
        cb = record->cb;
        invalidate = record->invalidate;
        writeBack = record->writeback;
        pendInvTable.erase(addr);
    }
#endif
    cb = record->cb;
    invalidate = record->invalidate;
    writeBack = record->writeback;
    pendInvTable.erase(addr);

    if(invalidate)
        realInvalidate(addr, size, writeBack);

    if(cb)
        EventScheduler::schedule((TimeDelta_t) 2, cb);
#if 0
    I(pendInvTable.find(addr) != pendInvTable.end());
    CallbackBase *cb = 0;
    bool invalidate = false;
    bool writeBack = false;

    PendInvTable::iterator it = pendInvTable.find(addr);
    Entry *record = &(it->second);
    if(--(record->outsResps) <= 0) {
        cb = record->cb;
        invalidate = record->invalidate;
        writeBack = record->writeback;
        pendInvTable.erase(addr);
    }

    if(invalidate)
        realInvalidate(addr, size, writeBack);

    if(cb)
        EventScheduler::schedule((TimeDelta_t) 2, cb);
#endif
}

void SMPCache::realInvalidate(PAddr addr, ushort size, bool writeBack)
{
    while(size) {

        Line *l = cache->findLine(addr);

        if (l) {
            nextSlot(); // counts for occupancy to invalidate line
            IJ(l->isValid());
            //I(l->isValid());
            if (l->isDirty()) {
                invalDirty.inc();
                if(writeBack)
                    doWriteBack(addr);
            }
            l->invalidate();

            // My Code
            listofInvalidTags->insert(l->prevTag);
        }
        addr += cache->getLineSize();
        size -= cache->getLineSize(); 
    }
}

// interface with protocol

// sends a request to lower level
void SMPCache::sendBelow(SMPMemRequest *sreq)
{
    sreq->goDown(missDelay, lowerLevel[0]);
}

void SMPCache::sendBelowI(SMPMemRequest *sreq)
{
    sreq->goDown(hitDelay, lowerLevel[0]);
}


// sends a response to lower level
// writes data back if protocol determines so
void SMPCache::respondBelow(SMPMemRequest *sreq)
{
    PAddr addr = sreq->getPAddr();

#if 0
    if(sreq->getSupplier() == this && sreq->needsWriteDown()) {
        doWriteBack(addr);
    }
#endif

    lowerLevel[0]->access(sreq);
}

// receives requests from other caches
void SMPCache::receiveFromBelow(SMPMemRequest *sreq) {
    IJ(0);
    //doReceiveFromBelowCB::scheduleAbs(nextSlot() + missDelay, this, sreq);
}

void SMPCache::doReceiveFromBelow(SMPMemRequest *sreq)
{
#if 0
    MemOperation memOp = sreq->getMemOperation();

    // request from other caches, need to process them accordingly

    if(memOp == MemRead) {
        protocol->readMissHandler(sreq);
        return;
    }

    if(memOp == MemReadW) {
        if(sreq->needsData())
            protocol->writeMissHandler(sreq);
        else
            protocol->invalidateHandler(sreq);
        return;
    }

    if(memOp == MemWrite) {
        I(!sreq->needsData());
        protocol->invalidateHandler(sreq);
        return;
    }
#endif

    I(0); // this routine should not be called for any other memory request
}

#if 0
void SMPCache::updateDirectory(SMPMemRequest *sreq) {
    // If there is pending writeback request, wait
    PAddr addr = sreq->getPAddr();
#if 0
    IJ(pendingWriteBackReq.find(addr)!=pendingWriteBackReq.end());

    if(pendingWriteBackReq[addr]) {
        Time_t nextTry = globalClock+1;
        doUpdateDirectoryCB::scheduleAbs(nextTry, this, sreq);
        return;
    }
    pendingWriteBackReq.erase(addr);
#endif
    // Update & unlock directory
    sendUpdateDirectory(sreq);
}
#endif

#if 0
void SMPCache::sendUpdateDirectory(SMPMemRequest *sreq)  {
    PAddr addr = sreq->getPAddr();

    SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, MeshDirUpdate);
    nsreq->addDstNode(getHomeNodeID(addr));

    sreq->destroy();

    nsreq->goDown(0, lowerLevel[0]);

    DEBUGPRINT("   [%s] sending directory update to %d for %x at %lld\n",
               getSymbolicName(), getHomeNodeID(addr), addr, globalClock);
}
#endif

void SMPCache::remoteAccess(MemRequest *mreq) {
    doReadRemoteCB::scheduleAbs(nextSlot(), this, mreq);
}

#if 0
void SMPCache::resolveSituation(SMPMemRequest *sreq) {
    MeshOperation meshOp = sreq->getMeshOperation();
    PAddr addr = sreq->getPAddr();
    switch(meshOp) {
    case IntervSharedRequest:
    {
        SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, SharedResponse);
        nsreq->addDst(sreq->msgOwner);

        DEBUGPRINT("   [%s] Resolving deadlock.. just reply: sends an shared response to %s for %x at %lld\n",
                   getSymbolicName(), sreq->msgOwner->getSymbolicName(), addr, globalClock);

        nsreq->goDown(hitDelay, lowerLevel[0]);
    }
    break;

    case IntervExRequest:
    {
        SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, ExclusiveResponse);
        nsreq->addDst(sreq->msgOwner);

        DEBUGPRINT("   [%s] Resolving deadlock.. just reply: sends an exclusive response to %s for %x at %lld\n",
                   getSymbolicName(), sreq->msgOwner->getSymbolicName(), addr, globalClock);

        nsreq->goDown(hitDelay, lowerLevel[0]);
    }
    break;
    default:
        IJ(0);
        //printf("Shouldn't be here %s at %llu\n", SMPMemRequest::SMPMemReqStrMap[meshOp], globalClock);
    }
}
#endif

void SMPCache::doReadRemote(MemRequest *mreq) {
    PAddr addr = mreq->getPAddr();
    SMPMemRequest *sreq = static_cast<SMPMemRequest *>(mreq);
    MeshOperation meshOp = sreq->getMeshOperation();
    Line *l = cache->readLine(addr);

    PAddr taddr = calcTag(addr);

    if(writeBackPending.find(taddr)!=writeBackPending.end()) {
        //IJ(l && l->getState()==DMESI_TRANS_INV);
        DEBUGPRINT("   [%s] Racing condition. Intervention ignored for %x (%x) at %lld\n",
                   getSymbolicName(), addr, taddr, globalClock);

        writeBackPending.erase(taddr);

        DEBUGPRINT("   [%s] Erase writeBackPending %x (%x) at %lld\n",
                   getSymbolicName(), addr, taddr, globalClock);

        sreq->destroy();

        return;
    }


    if(l && l->isLocked()) {
#if 0
        Time_t nextTry = globalClock+1;
        DEBUGPRINT("    ** [%s] remote cache entry locked (state %x) %x (from %s) at %lld\n", getSymbolicName()
                   , l->getState()
                   , addr
                   , sreq->msgOwner->getSymbolicName(), globalClock);
        doReadRemoteCB::scheduleAbs(nextTry, this, mreq);
#endif
        DEBUGPRINT("   [%s] remote cache entry locked (state %x) %x (from %s) at %lld\n", getSymbolicName()
                   , l->getState()
                   , addr
                   , sreq->msgOwner->getSymbolicName(), globalClock);
        IJ(pendRemoteRead.find(taddr)==pendRemoteRead.end());
        pendRemoteRead[taddr] = doReadRemoteCB::create(this, mreq);
        DEBUGPRINT("   [%s] pendRemoteRead add %x (%x), %p at %lld\n",
                   getSymbolicName(),
                   addr,
                   taddr, mreq,
                   globalClock);
        return;
    }

    switch(meshOp) {
    case IntervSharedRequest:
        if(l && l->canBeRead() && l->isDirty()) {
            // If owner has a dirty copy
            // it sends an shared response to the requestor and a sharing
            // writeback to the directory.
            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, SharedResponse);
                nsreq->addDst(sreq->msgOwner);

                DEBUGPRINT("   [%s] Owner has a dirty copy:  sends an shared response to %s for %x at %lld\n",
                           getSymbolicName(), sreq->msgOwner->getSymbolicName(),  addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, SharingWriteBack);
                nsreq->addDst(sreq->getRequestor());


                DEBUGPRINT("   [%s] Sends a sharing writeback with to the directory %s for %x at %lld\n",
                           getSymbolicName(), sreq->getRequestor()->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            // do write back
            //
            //
#if 0
            SMPMemRequest *nnnsreq = SMPMemRequest::create(this, addr, MemPush, true, 0, MeshMemWriteBack);
            nnnsreq->addDstNode(getL2NodeID(addr));
            nnnsreq->msgOwner = this;
            //nnsreq->saveSrc = sreq->getSrcNode();
            nnnsreq->goDown(hitDelay, lowerLevel[0]);
            DEBUGPRINT("   [%s] remote cache writeback to %d on %x at %lld\n",
                       getSymbolicName(), getL2NodeID(addr), addr, globalClock);
            //
            //
#endif

            protocol->changeState(l, DMESI_SHARED);

        } else if(l && l->getState()==DMESI_SHARED) {
            // for snooping
            // send sharing Tr(noTS) to directory
            // and sharing response
            // This is incomplete
            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, SharedResponse);
                nsreq->addDst(sreq->msgOwner);

                DEBUGPRINT("   [%s] Snooping Owner has a SHARED:  sends an shared response to %s for %x at %lld\n",
                           getSymbolicName(), sreq->msgOwner->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, SharingTransfer);
                nsreq->addDst(sreq->getRequestor());


                DEBUGPRINT("   [%s] Snooping Sends a sharing transfer with to the directory %s for %x at %lld\n",
                           getSymbolicName(), sreq->getRequestor()->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }


        } else if((l && l->getState()==DMESI_EXCLUSIVE) || !l) {
            // If owner has a clean-exclusive
            // or invalid copy it sends an shared ack (no data) to the requestor
            // and a sharing transfer (no data) to the directory.
            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, SharedAck);
                nsreq->addDst(sreq->msgOwner);

                DEBUGPRINT("   [%s] Owner has a clean copy:  sends an shared ack to %s for %x at %lld\n",
                           getSymbolicName(), sreq->msgOwner->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, SharingTransfer);
                nsreq->addDst(sreq->getRequestor());

                if(l && l->canBeRead()) {
                    IJ(l->getState()==DMESI_EXCLUSIVE);
                } else if(!l) {
                    DEBUGPRINT("   [%s] For snooping, TL hit before the owner for %x at %lld\n",
                               getSymbolicName(), addr, globalClock);
                } else {
                    IJ(0);
                }

                DEBUGPRINT("   [%s] Sends a sharing transfer with to the directory %s for %x at %lld\n",
                           getSymbolicName(),  sreq->getRequestor()->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            if(l && l->canBeRead()) {
                protocol->changeState(l, DMESI_SHARED);
            }
        } else {
            IJ(0);
        }
        sreq->destroy();
        break;

    case IntervExRequest:
        // Intervention shared received by owner. If owner has a dirty
        // copy it sends an exclusive response to the requestor and a
        // dirty transfer (no data) to the directory. If owner has a cleanexclusive
        // or invalid copy it sends an exclusive ack to the requestor
        // and a dirty transfer to the directory.
        //
        if(l && l->canBeRead() && l->isDirty()) {
            //IJ(l->getState()==DMESI_MODIFIED || l->getState()==DMESI_EXCLUSIVE);
            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, ExclusiveResponse);
                nsreq->addDst(sreq->msgOwner);

                DEBUGPRINT("   [%s] Owner has a dirty copy:  sends an exclusive response to %s for %x at %lld\n",
                           getSymbolicName(), sreq->msgOwner->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, DirtyTransfer);
                nsreq->addDst(sreq->getRequestor());

                DEBUGPRINT("   [%s] Sends a dirty transfer to the directory %s for %x at %lld\n",
                           getSymbolicName(), sreq->getRequestor()->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            DEBUGPRINT("   [%s] Invalidate %x for IntervExRequest at %lld\n",
                       getSymbolicName(), sreq->getPAddr(), globalClock);
            invalidateLine(addr, NULL, false);

        } else if(l && l->getState()==DMESI_SHARED) {
            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, ExclusiveResponse);
                nsreq->addDst(sreq->msgOwner);

                DEBUGPRINT("   [%s] Snooping Owner has a SHARED:  sends an exclusive response to %s for %x at %lld\n",
                           getSymbolicName(), sreq->msgOwner->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, DirtyTransfer);
                nsreq->addDst(sreq->getRequestor());

                DEBUGPRINT("   [%s] Snooping Sends a dirty transfer to the directory %s for %x at %lld\n",
                           getSymbolicName(), sreq->getRequestor()->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            DEBUGPRINT("   [%s] Invalidate %x for IntervExRequest at %lld\n",
                       getSymbolicName(), sreq->getPAddr(), globalClock);
            invalidateLine(addr, NULL, false);

        } else if((l && l->getState()==DMESI_EXCLUSIVE) || !l) {
            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, ExclusiveAck);
                nsreq->addDst(sreq->msgOwner);
                if(l && l->canBeRead()) {
                } else if(!l) {
                    DEBUGPRINT("   [%s] For snooping, TL hit before owner for %x at %lld\n",
                               getSymbolicName(), addr, globalClock);
                } else {
                    IJ(0);
                }

                DEBUGPRINT("   [%s] Owner has a clean copy:  sends an exclusive response to %s for %x at %lld\n",
                           getSymbolicName(), sreq->msgOwner->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }

            {
                SMPMemRequest *nsreq = SMPMemRequest::create(sreq, this, DirtyTransfer);
                nsreq->addDst(sreq->getRequestor());

                DEBUGPRINT("   [%s] Sends a dirty transfer to the directory %s for %x at %lld\n",
                           getSymbolicName(), sreq->getRequestor()->getSymbolicName(), addr, globalClock);

                nsreq->goDown(hitDelay, lowerLevel[0]);
            }
            if(l && l->canBeRead()) {
                invalidateLine(addr, NULL, false);
            }
        } else {
            IJ(0);
        }

        sreq->destroy();

        break;
    default:
        break;
    };

#if 0
    if(!l) {
#if 0
        IJ(0);
        DEBUGPRINT("********** [%s] I don't have %x. Inconsistency with directory at %lld!\n",
                   getSymbolicName(), addr, globalClock);
#endif
        resolveSituation(sreq);
        return;
    }

    if(!l->canBeRead()) {
        if (l->isLocked()) {
            Time_t nextTry = globalClock+1;
            DEBUGPRINT("    ** [%s] remote cache entry locked %x at %lld\n", getSymbolicName(), addr, globalClock);
            doReadRemoteCB::scheduleAbs(nextTry, this, mreq);
            return;
        } else {
#if 0
            IJ(0);
            DEBUGPRINT("********* [%s] ERROR in accessing remote cache. Locked %x %lld\n",
                       getSymbolicName(), addr, globalClock);
#endif
            resolveSituation(sreq);
            return;
        }
    } else {
        DEBUGPRINT("   [%s] remote cache access hit %x with state %x at %lld\n",
                   getSymbolicName(), addr, l->getState(), globalClock);
    }
#endif
}

void SMPCache::processReply(MemRequest *mreq) {
    SMPMemRequest *sreq = static_cast<SMPMemRequest *>(mreq);
    PAddr addr = mreq->getPAddr();

    DEBUGPRINT("   [%s] Processing Reply from %s for %x at %lld\n",
               getSymbolicName(), sreq->getRequestor()->getSymbolicName(), sreq->getPAddr(), globalClock);

    //if(pendingReplyFlag.find(addr)!=pendingReplyFlag.end() &&
    //		pendingSpecFlag.find(addr)!=pendingSpecFlag.end()) {
    //	if(pendingReplyFlag[addr] && pendingSpecFlag[addr]) {
    //		pendingReplyFlag.erase(addr);
    //		pendingSpecFlag.erase(addr);
    //
    DEBUGPRINT("   [%s] Reply Done for %x at %lld\n",
               getSymbolicName(), sreq->getPAddr(), globalClock);
    if(sreq->getMemOperation()==MemRead) {
        sreq->isExcl = false;
        //sreq->isOwner = true;
        protocol->readMissAckHandler(sreq);
    } else {
        protocol->writeMissAckHandler(sreq);
    }
    return;

    //	}
    //}
    //DEBUGPRINT("   [%s] Reply Still Waiting... for %x at %lld\n",
    //		getSymbolicName(), sreq->getPAddr(), globalClock);
    //sreq->destroy();
}

void SMPCache::returnAccess(MemRequest *mreq)
{
    SMPMemRequest *sreq = static_cast<SMPMemRequest *>(mreq);
    //MemOperation memOp = mreq->getMemOperation();
    MeshOperation meshOp = sreq->getMeshOperation();
    PAddr addr = mreq->getPAddr();
    PAddr taddr = calcTag(addr);

    switch(meshOp) {
    case ReadRequest:
    case WriteRequest:
    case UpgradeRequest:
        // Me should be the home directory
        // Not anoy more for COHOPT
        break;
#if 0
    case ForwardRequest:
        if(sreq->msgDst == this) {
            remoteAccess(mreq);
        }
        break;
#endif
    case ExclusiveReply:
        if(sreq->msgOwner == this) {
            if(sreq->getMemOperation()==MemRead) {
                sreq->isExcl = true;
                //sreq->isOwner = false;
                protocol->readMissAckHandler(sreq);
            } else {
                protocol->writeMissAckHandler(sreq);
            }
        }
        break;

    case SharedReply:
        if(sreq->msgOwner == this) {
            sreq->isExcl = false;
            //sreq->isOwner = false;
            protocol->readMissAckHandler(sreq);
        }
        break;
    case SpeculativeReply:
        if(sreq->msgDst == this) {
            DEBUGPRINT("   [%s] Received %s  from %s for %x at %lld\n",
                       getSymbolicName(), SMPMemRequest::SMPMemReqStrMap[meshOp],
                       sreq->getRequestor()->getSymbolicName(), sreq->getPAddr(), globalClock);
            if(replyReady.find(taddr)==replyReady.end()) {
                DEBUGPRINT("   [%s] Not yet ready for %x at %lld\n",
                           getSymbolicName(), sreq->getPAddr(), globalClock);
                replyReady[taddr] = true;
                sreq->destroy();
            } else {
                //IJ(replyReady[taddr]==true);
                DEBUGPRINT("   [%s] replyReady for %x \n", getSymbolicName(), addr);
                replyReady.erase(taddr);
                processReply(mreq);
            }
        }
        break;
    case SharedResponse:
    case SharedAck:
        if(sreq->msgDst == this) {
            DEBUGPRINT("   [%s] Received %s from %s for %x at %lld\n",
                       getSymbolicName(),
                       SMPMemRequest::SMPMemReqStrMap[meshOp],
                       sreq->getRequestor()->getSymbolicName(), sreq->getPAddr(), globalClock);
            if(replyReady.find(taddr)==replyReady.end()) {
                DEBUGPRINT("   [%s] Not yet ready for %x at %lld\n",
                           getSymbolicName(), sreq->getPAddr(), globalClock);
                replyReady[taddr] = true;
                sreq->destroy();
            } else {
                IJ(replyReady[taddr]==true);
                DEBUGPRINT("   [%s] replyReady for %x at \n", getSymbolicName(), addr);
                replyReady.erase(taddr);
                processReply(mreq);
            }
        }
        break;
    case ExclusiveResponse:
    case ExclusiveAck:
        if(sreq->msgDst == this) {
            DEBUGPRINT("   [%s] Received Exclusive Response/Ack from %s for %x at %lld\n",
                       getSymbolicName(), sreq->getRequestor()->getSymbolicName(), sreq->getPAddr(), globalClock);
            if(replyReady.find(taddr)==replyReady.end()) {
                DEBUGPRINT("   [%s] Not yet ready for %x at %lld\n",
                           getSymbolicName(), sreq->getPAddr(), globalClock);
                replyReady[taddr] = true;
                sreq->destroy();
            } else {
                IJ(replyReady[taddr]==true);
                DEBUGPRINT("   [%s] replyReady for %x at\n", getSymbolicName(), addr);
                replyReady.erase(taddr);
                processReply(mreq);
            }
        }
        break;
    case Invalidation:
        if(sreq->dstObj.find(this)!=sreq->dstObj.end()) {
            DEBUGPRINT("   [%s] Received Invalidation message from %d for %x at %lld\n",
                       getSymbolicName(), sreq->getSrcNode(), sreq->getPAddr(), globalClock);
            protocol->invalidateHandler(sreq);
        }
        break;
    case ExclusiveReplyInvND:
        if(sreq->msgOwner==this) {
            DEBUGPRINT("   [%s] Upgrade for %x at %lld\n",
                       getSymbolicName(), sreq->getPAddr(), globalClock);
        }
    case ExclusiveReplyInv:
        if(sreq->msgOwner==this) {
            DEBUGPRINT("   [%s] Exclusive Reply with invalidation pending received (%d pending) for %x at %lld\n",
                       getSymbolicName(), sreq->nInv, sreq->getPAddr(), globalClock);
            if(sreq->nInv==0) {
                protocol->writeMissAckHandler(sreq);
            } else {
                IJ(invCounter.find(addr)==invCounter.end());
                invCounter[addr] = sreq->nInv;
                if(pendingInvCounter.find(addr)!=pendingInvCounter.end()) {
                    if(pendingInvCounter[addr] == invCounter[addr]) {
                        protocol->finalizeInvReply(sreq);
                        break;
                    }
                }
                sreq->destroy();
            }
        }
        break;
    case InvalidationAck:
        if(sreq->msgOwner==this) {
            protocol->invalidateReplyHandler(sreq);
        }
        break;
    case IntervSharedRequest:
    case IntervExRequest:
        if(sreq->msgDst == this) {
            DEBUGPRINT("   [%s] Intervention signal for %x at %lld\n",
                       getSymbolicName(), sreq->getPAddr(), globalClock);

            remoteAccess(mreq);
        }
        break;

    case WriteBackExAck:
        if(sreq->msgDst==this) {
            IJ(writeBackPending.find(calcTag(addr))!=writeBackPending.end());
            DEBUGPRINT("   [%s] Normal writeback. erase writeBackPending %x (%x) at %lld\n",
                       getSymbolicName(), addr, calcTag(addr), globalClock);
            writeBackPending.erase(calcTag(addr));
            processInvDirAck(sreq);
        }
        break;

    case WriteBackBusyAck:
        if(sreq->msgDst==this) {
            DEBUGPRINT("   [%s] Writeback busy ack signal for %x at %lld\n",
                       getSymbolicName(), sreq->getPAddr(), globalClock);
            //IJ(writeBackPending.find(calcTag(addr))==writeBackPending.end());
#if 0
            if(writeBackPending.find(calcTag(addr))!=writeBackPending.end()) {
                DEBUGPRINT("   [%s] Writeback busy: writeBackPending exist, clean for %x (%x) at %lld\n",
                           getSymbolicName(), sreq->getPAddr(),
                           calcTag(addr),
                           globalClock);
                writeBackPending.erase(calcTag(addr));
            }
#endif
            processInvDirAck(sreq);
        }
        break;

    case NAK:
        // Again!
        //if(sreq->msgOwner == this) {
        if(sreq->msgDst == this) {

            if(pendingInv.find(taddr)!=pendingInv.end()) {
                pendingInv.erase(taddr);
                DEBUGPRINT("   [%s] Snoop NAK'd cleaning pending Inv for %x at %lld\n",
                           getSymbolicName(), sreq->getPAddr(), globalClock);
            }


            DEBUGPRINT("   [%s] NAK'd, cleaning resource and retry for %x at %lld\n",
                       getSymbolicName(), sreq->getPAddr(), globalClock);

            PAddr taddr = calcTag(addr);

            protocol->freeResource(mreq);

            if(pendRemoteRead.find(taddr)!=pendRemoteRead.end()) {
                DEBUGPRINT("   [%s] Handling Pending Intervs for %x (%x) at %lld\n",
                           getSymbolicName(), addr, taddr, globalClock);
                CallbackBase *cb = pendRemoteRead[taddr];
                pendRemoteRead.erase(taddr);
                IJ(cb);
                cb->call();
            }

            if(sreq->getMemOperation()==MemRead) {
                doReadAgainCB::scheduleAbs(globalClock+2, this, sreq->getOriginalRequest());
                //protocol->sendReadMiss(sreq->getOriginalRequest());
            } else {
                doWriteAgainCB::scheduleAbs(globalClock+2, this, sreq->getOriginalRequest());
                //protocol->sendWriteMiss(sreq->getOriginalRequest());
            }
            sreq->destroy();
        }
        break;
    case MeshMemAccessReply:
        break;
    default:
        break;
    };

#if 0
    if(meshOp == ReadRequest) { // Me should be the home directory
        //
    } else if (meshOp == MeshDirReply) {
        if(sreq->msgOwner==this) {
            DEBUGPRINT("   [%s] got directory access reply ty %d received at %d from %d for %x at %lld  (%p)\n",
                       getSymbolicName(), sreq->getMemOperation(), getNodeID(), sreq->getSrcNode(), sreq->getPAddr(), globalClock, mreq);
            protocol->dirReplyHandler(sreq);
        }
    } else if (meshOp == MeshMemRequest) {
        // Do nothing
    } else if (meshOp == MeshMemAccessReply) {
        // Do nothing
    } else if (meshOp == MeshMemReply) {
        if(sreq->msgOwner==this) {
            DEBUGPRINT("   [%s] got L2 access reply ty %d received at %d from %d for %x at %lld\n",
                       getSymbolicName(), sreq->getMemOperation(), getNodeID(), sreq->getSrcNode(), sreq->getPAddr(), globalClock);
            updateDirectory(sreq);
        }
    } else if (meshOp == MeshDirUpdate) {
        // Do nothing
    } else if (meshOp == MeshReadDataRequest) {
        if(sreq->msgDst == this) {
            DEBUGPRINT("   [%s] got remote cache access ty %d received at %d from %d for %x at %lld\n",
                       getSymbolicName(), sreq->getMemOperation(), getNodeID(), sreq->getSrcNode(), sreq->getPAddr(), globalClock);
            remoteAccess(mreq);
        }
    } else if (meshOp == MeshReadDataReply) {
        if(sreq->msgOwner==this) {
            DEBUGPRINT("   [%s] got remote cache access reply ty %d received at %d from %d for %x at %lld\n",
                       getSymbolicName(), sreq->getMemOperation(), getNodeID(), sreq->getSrcNode(), sreq->getPAddr(), globalClock);

#if 0
            if(!sreq->writeBack) {
                pendingWriteBackReq[addr] = false;
            }
#endif

            updateDirectory(sreq);
        }
    } else if (meshOp == MeshMemWriteBack) {
        // Do nothing
#if 0
    } else if (meshOp == MeshMemWriteBackReply) {
        if(sreq->msgOwner==this) {
            DEBUGPRINT("   [%s] got write back reply at %d from %d for %x at %lld\n",
                       getSymbolicName(), getNodeID(), sreq->getSrcNode(), sreq->getPAddr(), globalClock);
            pendingWriteBackReq[addr] = false;
            sreq->destroyAll();
        }
#endif
    } else if (meshOp == MeshDirUpdateAck) {
        // Update cache
        if(sreq->msgOwner==this) {
            if(sreq->getMemOperation()==MemRead) {
                protocol->readMissAckHandler(sreq);
            } else {
                protocol->writeMissAckHandler(sreq);
            }
        }
        //------------------------------------ READ done -----------------------------------------------
#if 0
    } else if (meshOp == MeshWriteReply) {
        if(sreq->msgOwner==this) {
            DEBUGPRINT("   [%s] write reply received at %d from %d for %x at %lld\n",
                       getSymbolicName(), getNodeID(), sreq->getSrcNode(), sreq->getPAddr(), globalClock);
            protocol->writeMissReplyHandler(sreq);
        }
#endif
    } else if (meshOp == MeshInvRequest) {
        if(sreq->dstObj.find(this)!=sreq->dstObj.end()) {
            protocol->invalidateHandler(sreq);
        }
    } else if (meshOp == MeshInvReply || meshOp == MeshInvDataReply) {
        if(sreq->msgOwner==this) {
            protocol->invalidateReplyHandler(sreq);
        }
    } else if (meshOp == MeshInvDirUpdate) {
        //
    } else if (meshOp == MeshInvDirAck) {
        if(sreq->msgOwner==this) {
            processInvDirAck(sreq);
        }
    } else if (meshOp == MeshWriteDataRequest) {
        if(sreq->msgDst == this) {
            DEBUGPRINT("   [%s] got remote cache access (for write) ty %d received at %d from %d for %x at %lld\n",
                       getSymbolicName(), sreq->getMemOperation(), getNodeID(), sreq->getSrcNode(), sreq->getPAddr(), globalClock);
            remoteAccess(mreq);
        }
    } else {
        return;
        //IJ(0);
    }
#endif

#if 0
    if(sreq->getRequestor() == this) {
        // request from this cache (response is ready)

        if(memOp == MemRead ) {
            protocol->readMissAckHandler(sreq);
        }
        else if(memOp == MemReadW) {
            if(sreq->needsData()) {
                protocol->writeMissAckHandler(sreq);
            } else {
                I(sreq->needsSnoop());
                protocol->invalidateAckHandler(sreq);
            }
        }
        else if(memOp == MemWrite) {
            I(!sreq->needsData());
            I(sreq->needsSnoop());
            protocol->invalidateAckHandler(sreq);
        }
        else if(memOp == MemPush) {
            protocol->writeBackAckHandler(sreq);
        }
    } else {
        receiveFromBelow(sreq);
    }
#endif
}

void SMPCache::concludeAccess(MemRequest *mreq)
{
    PAddr addr = mreq->getPAddr();

    if(mreq->getMemOperation()==MemRead) {
        DEBUGPRINT("[%s] read done %x at %lld\n",
                   getSymbolicName(), addr, globalClock);
    } else {
        DEBUGPRINT("[%s] write done %x at %lld\n",
                   getSymbolicName(), addr, globalClock);
    }

#if (defined DLCHECK)
    Cache::dlcnt++;
#endif

    mreq->mutateReadToWrite(); /*
                              Hack justification: It makes things much
                              nicer if we can call mutateWriteToRead()
                              in write() if the line is displaced from
                              the cache between the time the write is
                              processed in the L1 to the time it is
                              processed in the L2.

                              BUT from the L2, we don't call
                              mreq->goDown(), so we can't rely on
                              mreq->goUp() to restore the memOp.
                            */
    mreq->goUp(0);


    PAddr taddr = calcTag(addr);


    if(pendingInv.find(taddr)!=pendingInv.end()) {
        Line *l = getLine(addr);
        IJ(l);
            
		DEBUGPRINT("   [%s] pending Invalidation, invalidate %x at %lld\n"
                       , getSymbolicName(), addr, globalClock);
        
		l->invalidate();
        pendingInv.erase(taddr);
    }

    if(pendRemoteRead.find(taddr)!=pendRemoteRead.end()) {
        DEBUGPRINT("   [%s] Handling Pending Intervs for %x (%x) at %lld\n",
                   getSymbolicName(), addr, taddr, globalClock);
        CallbackBase *cb = pendRemoteRead[taddr];
        pendRemoteRead.erase(taddr);
        IJ(cb);
        cb->call();
    }

    outsReq->retire(addr);
    //mutExclBuffer->retire(addr);
//#if (defined SIGDEBUG)
#if (defined CHECK_STALL)
    lastFin = globalClock;
#endif
//#endif

}

void SMPCache::sendInvDirUpdate(PAddr rpl_addr, PAddr new_addr, CallbackBase *cb, bool wb, bool tk) {
    IJ((wb&&tk)==false);
    if(wb||tk) {
        SMPMemRequest *sreq;
        //if(wb) {
        sreq = SMPMemRequest::create(this, rpl_addr, MemPush, false, 0, WriteBackRequest);
        //} else {
        //    sreq = SMPMemRequest::create(this, rpl_addr, MemPush, false, 0, TokenBackRequest);
        //}
        sreq->newAddr = new_addr;
        sreq->invCB = cb;
        sreq->addDstNode(getHomeNodeID(rpl_addr));
        sreq->msgOwner = this;

        sreq->goDown(0, lowerLevel[0]);
        DEBUGPRINT("   [%s] Sending %s for %x (to access %x) at %llu (%p)\n"
                   , getSymbolicName()
                   , MemOperationStr[sreq->getMemOperation()]
                   , rpl_addr
                   , new_addr
                   , globalClock
                   , sreq);

        IJ(writeBackPending.find(calcTag(rpl_addr))==writeBackPending.end());
        writeBackPending[calcTag(rpl_addr)] = true;
        DEBUGPRINT("   [%s] setting writeBackPending %x (%x) to %d at %llu \n"
                   , getSymbolicName()
                   , rpl_addr
                   , calcTag(rpl_addr)
                   , writeBackPending[calcTag(rpl_addr)]
                   , globalClock);
    } else {

        Line *l = cache->findLine(rpl_addr);
        IJ(l);
        IJ(l->getState()==SMP_TRANS_INV);

        l->setTag(calcTag(new_addr));
        //listofInvalidTags->erase(l->prevTag);  // My CODE
        l->changeStateTo(SMP_TRANS_RSV);

        DEBUGPRINT("   [%s] Invalidating clean line %x silently at %llu \n"
                   , getSymbolicName()
                   , rpl_addr
                   , globalClock);

        cb->call();
    }
}

void SMPCache::processInvDirAck(SMPMemRequest *sreq) {

    DEBUGPRINT("   [%s] invalidate (writeback) ack from %d for %x (replace to %x) at %lld (0x%lx)\n",
               getSymbolicName(), sreq->getSrcNode(), sreq->getPAddr(), sreq->newAddr, globalClock, (uint64_t)sreq);

    PAddr rpl_addr = sreq->getPAddr();
    PAddr addr = sreq->newAddr;
    CallbackBase *cb = sreq->invCB;
    sreq->invCB = NULL;

    Line *l = cache->findLine(rpl_addr);
    IJ(l);
    IJ(l->getState()==SMP_TRANS_INV);

    l->setTag(calcTag(addr));
    //listofInvalidTags->erase(l->prevTag); // My code
    l->changeStateTo(SMP_TRANS_RSV);

#if 0
    Directory *dir = SMPSliceCache::globalDirMap[getHomeNodeID(rpl_addr)];
    DirectoryEntry *de = dir->find(rpl_addr);
    IJ(de->isBusy());
    //IJ(de->isLocked());
    de->unsetBusy();
    //de->setLock(false);
#endif
    sreq->destroy();

    IJ(cb);
    cb->call();
}

SMPCache::Line *SMPCache::allocateLine(PAddr addr, CallbackBase *cb,
                                       bool canDestroyCB)
{
    PAddr rpl_addr = 0;
    I(cache->findLineDebug(addr) == 0);
    Line *l = cache->findLine2Replace(addr);

    if(!l) {
        // need to schedule allocate line for next cycle
        doAllocateLineCB::scheduleAbs(globalClock+1, this, addr, 0, cb);
        return 0;
    }

    rpl_addr = cache->calcAddr4Tag(l->getTag());
    lineFill.inc();

    nextSlot(); // have to do an access to check which line is free

    if(!l->isValid()) {
        if(canDestroyCB)
            cb->destroy();
        l->setTag(cache->calcTag(addr));
        listofInvalidTags->erase(l->prevTag); // My Code
        DEBUGPRINT("   [%s] allocated free line for %x at %lld \n",
                   getSymbolicName(), addr , globalClock);
        cacheHelper -> lruStack -> updateLRUStack(calcTag(addr)); 
        return l;
    }
    DEBUGPRINT("   [%s] allocated line %x for %x at %lld \n",
               getSymbolicName(), rpl_addr, addr , globalClock);

#if 0
    Directory *dir = SMPSliceCache::globalDirMap[getHomeNodeID(rpl_addr)];
    DirectoryEntry *de = dir->find(rpl_addr);
    if(de->isBusy()) {
        //if(de->isLocked()) {
        // need to schedule allocate line for next cycle
        DEBUGPRINT("   [%s] allocation fail : directory locked %x at %lld \n",
                   getSymbolicName(), addr , globalClock);
        doAllocateLineCB::scheduleAbs(globalClock+1, this, addr, 0, cb);
        return 0;
    }

    de->setBusy();
#endif

    if(isHighestLevel()) {
        bool wb = false;
        bool tk = false;
        if(l->isDirty()) {
            allocDirty.inc();
            doWriteBack(rpl_addr);
            wb = true;
            //data = true;
        }
        
        //l->setTag(cache->calcTag(addr));
        listofInvalidTags->erase(l->prevTag);
        cacheHelper -> lruStack -> updateLRUStack(calcTag(addr));
        //return l;

#if 0
        if(canDestroyCB)
            cb->destroy();
        l->invalidate();
        l->setTag(cache->calcTag(addr));
        return l;
#endif
#if 1
        DEBUGPRINT("   [%s] INVALIDATE line %x (dirty? %d) changed from %x at %lld (for %x)\n",
                   getSymbolicName(), cache->calcAddr4Tag(l->getTag()), wb, l->getState(), globalClock, addr);

        if(l->getState()==MESI_EXCLUSIVE) {
            //wb = true;
            tk = true;
            DEBUGPRINT("   [%s] INVALIDATE %x because its Exclusive at %lld (for %x)\n",
                       getSymbolicName(), rpl_addr, globalClock, addr);
        }
        if(l->getState()==MESI_SHARED) {
            //tk = true;
            //DEBUGPRINT("   [%s] INVALIDATE %x because its Shared with Token at %lld (for %x)\n",
            //		getSymbolicName(), rpl_addr, globalClock, addr);
        }

        l->changeStateTo(SMP_TRANS_INV);

        DEBUGPRINT("   [%s] INVALIDATE %x at %lld (for %x)\n",
                   getSymbolicName(), rpl_addr, globalClock, addr);
        DEBUGPRINT("   [%s] INVALIDATE line %x changed to %x at %lld (for %x)\n",
                   getSymbolicName(), cache->calcAddr4Tag(l->getTag()), l->getState(), globalClock, addr);

        sendInvDirUpdate(rpl_addr, addr, cb, wb, tk);

        
        return 0; // We need to send message back and forth
    }

    IJ(0);
    return 0;
#endif
#if 0
    I(pendInvTable.find(rpl_addr) == pendInvTable.end());
    pendInvTable[rpl_addr].outsResps = getNumCachesInUpperLevels();
    pendInvTable[rpl_addr].cb = doAllocateLineCB::create(this, addr, rpl_addr, cb);
    pendInvTable[rpl_addr].invalidate = false;
    pendInvTable[rpl_addr].writeback = true;

    protocol->preInvalidate(l);

    invUpperLevel(rpl_addr, cache->getLineSize(), this);

    return 0;
#endif

#if 0
    PAddr rpl_addr = 0;
    I(cache->findLineDebug(addr) == 0);
    Line *l = cache->findLine2Replace(addr);

    if(!l) {
        // need to schedule allocate line for next cycle
        doAllocateLineCB::scheduleAbs(globalClock+1, this, addr, 0, cb);
        return 0;
    }

    rpl_addr = cache->calcAddr4Tag(l->getTag());
    lineFill.inc();

    nextSlot(); // have to do an access to check which line is free

    if(!l->isValid()) {
        if(canDestroyCB)
            cb->destroy();
        l->setTag(cache->calcTag(addr));
        return l;
    }

    if(isHighestLevel()) {
        if(l->isDirty()) {
            allocDirty.inc();
            doWriteBack(rpl_addr);
        }

        if(canDestroyCB)
            cb->destroy();
        l->invalidate();
        l->setTag(cache->calcTag(addr));
        DEBUGPRINT("   [%s] INVALIDATE %x at %lld (for %x)\n",
                   getSymbolicName(), rpl_addr, globalClock, addr);
        return l;
    }

    I(pendInvTable.find(rpl_addr) == pendInvTable.end());
    pendInvTable[rpl_addr].outsResps = getNumCachesInUpperLevels();
    pendInvTable[rpl_addr].cb = doAllocateLineCB::create(this, addr, rpl_addr, cb);
    pendInvTable[rpl_addr].invalidate = false;
    pendInvTable[rpl_addr].writeback = true;

    protocol->preInvalidate(l);

    invUpperLevel(rpl_addr, cache->getLineSize(), this);

    return 0;
#endif
}

void SMPCache::doAllocateLine(PAddr addr, PAddr rpl_addr, CallbackBase *cb)
{
    // this is very dangerous (don't do it at home) if rpl_addr is zero,
    // it means allocateLine was not able to allocate a line at its last
    // try probably because all lines in the set were
    // locked. allocateLine has scheduled a callback to doAllocateLine
    // in the next cycle, with rpl_addr zero. The code below will call
    // allocateLine again, which will schedule another doAllocateLine if
    // necessary. If that happens, allocateLine will return 0, which
    // means doAllocateLine shouldn't do anything else. If allocateLine
    // returns a line, then the line was successfully allocated, and all
    // that's left is to call the callback allocateLine has initially
    // received as a parameter
    if(!rpl_addr) {
        Line *l = allocateLine(addr, cb, false);

        if(l) {
            I(cb);
            l->setTag(calcTag(addr));
            listofInvalidTags->erase(l->prevTag);
            l->changeStateTo(SMP_TRANS_RSV);
            cb->call();
        }

        return;
    }

    IJ(0);

    Line *l = cache->findLine(rpl_addr);
    I(l && l->isLocked());

    if(l->isDirty()) {
        allocDirty.inc();
        doWriteBack(rpl_addr);
    }

    I(cb);
    l->setTag(cache->calcTag(addr));
    listofInvalidTags->erase(l->prevTag);
    l->changeStateTo(SMP_TRANS_RSV);
    cb->call();
}

SMPCache::Line *SMPCache::getLine(PAddr addr)
{
    nextSlot();
    return cache->findLine(addr);
}

void SMPCache::writeLine(PAddr addr) {
    Line *l = cache->writeLine(addr);
    IJ(l);
}

void SMPCache::invalidateLine(PAddr addr, CallbackBase *cb, bool writeBack)
{
    Line *l = cache->findLine(addr);

    IJ(l);

    IJ(pendInvTable.find(addr) == pendInvTable.end());
    pendInvTable[addr].outsResps = getNumCachesInUpperLevels();
    pendInvTable[addr].cb = cb;
    pendInvTable[addr].invalidate = true;
    pendInvTable[addr].writeback = writeBack;

    protocol->preInvalidate(l);

    if(!isHighestLevel()) {
        IJ(0);
        invUpperLevel(addr, cache->getLineSize(), this);
        return;
    }

    doInvalidate(addr, cache->getLineSize());
#if 0
    Line *l = cache->findLine(addr);

    I(l);

    I(pendInvTable.find(addr) == pendInvTable.end());
    pendInvTable[addr].outsResps = getNumCachesInUpperLevels();
    pendInvTable[addr].cb = cb;
    pendInvTable[addr].invalidate = true;
    pendInvTable[addr].writeback = writeBack;

    protocol->preInvalidate(l);

    if(!isHighestLevel()) {
        invUpperLevel(addr, cache->getLineSize(), this);
        return;
    }

    doInvalidate(addr, cache->getLineSize());
#endif
}

int32_t SMPCache::getHomeNodeID(PAddr addr) {
    //int32_t dst = calcTag(addr) % getMaxNodeID();
    int32_t dst = getL2NodeID(addr);
    //printf("%x %x %d %d\n", addr, calcTag(addr),  addr, dst);
    return dst;
}

int32_t SMPCache::getL2NodeID(PAddr addr) {
    //int32_t dst = calcTag(addr) % getMaxNodeID();
	int32_t dst = bitSelect(calcTag(addr), nodeSelSht, getMaxNodeID_bit());
    return dst;
}

#ifdef SESC_SMP_DEBUG
void SMPCache::inclusionCheck(PAddr addr) {
    const LevelType* la = getUpperLevel();
    MemObj* c  = (*la)[0];

    const LevelType* lb = c->getUpperLevel();
    MemObj*    cc = (*lb)[0];

    I(!((Cache*)cc)->isInCache(addr));
}
#endif

#if (defined SIGDEBUG)
void SMPCache::pStat() {
    double total =   readMiss.getDouble()  + readHit.getDouble()
                     + writeMiss.getDouble() + writeHit.getDouble() + 1;

    printf("\t\tStat total=%8.0f:rdMiss=%8.0f:rdMissRate=%5.3f:wrMiss=%8.0f:wrMissRate=%5.3f\n"
           ,total
           ,readMiss.getDouble()
           ,100*readMiss.getDouble()  / total
           ,writeMiss.getDouble()
           ,100*writeMiss.getDouble() / total
          );

    HASH_MAP<PAddr, Time_t >::iterator it;
    for(it=debugTrack.begin(); it!=debugTrack.end(); it++) {
        printf("\t\t%x issued at %lld\n", it->first, it->second);
    }
    printf("\n");
    fflush(stdout);

#if 0
    printf("\t\tMSHR total %d rd %d wr %d\n",
           outsReq->getnEntries(),
           outsReq->getnReads(),
           outsReq->getnWrites());
#endif
}
#endif
