#################
# NICU network analysis, surveillance extension
# Citation: Goldstein ND, Jenness SM, Tuttle D, Power M, Paul DA. Evaluating a neonatal intensive care unit MRSA surveillance programme using agent-based network modelling. Manuscript in preparation.
# 11/14/17 -- Neal Goldstein
#################


### FUNCTIONS ###

library("EpiModel") #network modeling
library(gmodels) #CrossTable
library(psych) #describe, describeBy
library(RColorBrewer) #color palettes

## Modules for extending core functions of EpiModel

#custom birth function for fixed admission rate
admit.net = function(dat, at) {
  if (dat$param$vital == FALSE) {
    return(dat)
  }
  
  #new attribute tracks known colonization from surveillance
  if (at == 2) {
    dat$attr$status_known = rep(NA,length(dat$attr$status))
  }
  
  b.rate <- dat$param$b.rate
  
  modes <- dat$param$modes
  tea.status <- dat$control$tea.status
  nOld <- dat$epi$num[at - 1]
  nCurr <- network.size(dat$nw)
  b.rand <- dat$control$b.rand
  delete.nodes <- dat$control$delete.nodes
  nBirths <- 0
  newNodes <- NULL
  if (modes == 1 && nOld > 0) {
    
    #constant admit rate w/max of 70 infants in NICU allowed per unit design/policy
    nBirths = ifelse(nOld < 70, rbinom(1, 1, b.rate), 0)
    
    if (nBirths > 0) {
      dat$nw <- add.vertices(dat$nw, nv = nBirths)
      newNodes <- (nCurr + 1):(nCurr + nBirths)
      dat$nw <- activate.vertices(dat$nw, onset = at, terminus = Inf, v = newNodes)
    }
  }
  
  if (length(newNodes) > 0) {
    form <- get_nwparam(dat)$formation
    fterms <- get_formula_terms(form)
    curr.tab <- get_attr_prop(dat$nw, fterms)
    if (length(curr.tab) > 0) {
      dat$nw <- update_nwattr(dat$nw, newNodes, dat$control$attr.rules, curr.tab, dat$temp$t1.tab)
    }
    dat <- copy_toall_attr(dat, at, fterms)
    if (tea.status == TRUE) {
      dat$nw <- activate.vertex.attribute(dat$nw, prefix = "testatus", value = "s", onset = at, terminus = Inf, v = newNodes)
    }
    if (modes == 1) {
      
      #set proportion of admissions to prevalent MRSA colonization
      prev_colon = rbinom(length(newNodes), 1, dat$param$birth.prob)
      dat$attr$status <- c(dat$attr$status, c(rep("s", sum(prev_colon==0)), rep("i", sum(prev_colon==1))))
      
      dat$attr$active <- c(dat$attr$active, rep(1, length(newNodes)))
      dat$attr$infTime <- c(dat$attr$infTime, rep(NA, length(newNodes)))
      dat$attr$entrTime <- c(dat$attr$entrTime, rep(at, length(newNodes)))
      dat$attr$exitTime <- c(dat$attr$exitTime, rep(NA, length(newNodes)))
      
      #unknown (surveillance) colonization status when an admission
      dat$attr$status_known <- c(dat$attr$status_known, rep(NA, length(newNodes)))
      
    }
    newNodesInf <- intersect(newNodes, which(dat$attr$status == "i"))
    dat$attr$infTime[newNodesInf] <- at
    if (length(unique(sapply(dat$attr, length))) != 1) {
      stop("Attribute list of unequal length. Check births.net module.")
    }
  }
  
  #record total, susceptible, and infected admissions
  dat$epi$b.flow[at] <- nBirths
  dat$epi$bs.flow[at] <- ifelse(nBirths>0, sum(prev_colon==0), 0)
  dat$epi$bi.flow[at] <- ifelse(nBirths>0, sum(prev_colon==1), 0)
  dat$epi$capacity.nicu[at] = ifelse(nOld + nBirths>=70, T, F)
  
  return(dat)
}

#custom infection function for surveillance
surveil.net = function(dat, at) {
  
  active <- dat$attr$active
  status <- dat$attr$status
  modes <- dat$param$modes
  mode <- idmode(dat$nw)
  inf.prob <- dat$param$inf.prob
  
  act.rate <- dat$param$act.rate
  nw <- dat$nw
  tea.status <- dat$control$tea.status
  
  idsSus <- which(active == 1 & status == "s")
  idsInf <- which(active == 1 & status == "i")
  nActive <- sum(active == 1)
  nElig <- length(idsInf)
  nInf <- totInf <- 0
  if (nElig > 0 && nElig < nActive) {
    del <- discord_edgelist(dat, idsInf, idsSus, at)
    if (!(is.null(del))) {
      del$infDur <- at - dat$attr$infTime[del$inf]
      del$infDur[del$infDur == 0] <- 1
      linf.prob <- length(inf.prob)
      
      del$transProb <- ifelse(del$infDur <= linf.prob, inf.prob[del$infDur], inf.prob[linf.prob])
      
      if (!is.null(dat$param$inter.eff) && at >= dat$param$inter.start) {
        del$transProb <- del$transProb * (1 - dat$param$inter.eff)
      }
      lact.rate <- length(act.rate)
      del$actRate <- ifelse(del$infDur <= lact.rate, act.rate[del$infDur], act.rate[lact.rate])
      del$finalProb <- 1 - (1 - del$transProb)^del$actRate
      
      transmit <- rbinom(nrow(del), 1, del$finalProb)
      del <- del[which(transmit == 1), ]
      idsNewInf <- unique(del$sus)
      nInf <- sum(mode[idsNewInf] == 1)
      
      totInf <- nInf
      if (totInf > 0) {
        if (tea.status == TRUE) {
          nw <- activate.vertex.attribute(nw, prefix = "testatus",
                                          value = "i", onset = at,
                                          terminus = Inf, v = idsNewInf)
        }
        dat$attr$status[idsNewInf] <- "i"
        dat$attr$infTime[idsNewInf] <- at
      }
      if (any(names(nw$gal) %in% "vertex.pid")) {
        del$sus <- get.vertex.pid(nw, del$sus)
        del$inf <- get.vertex.pid(nw, del$inf)
      }
    }
  }
  if (totInf > 0) {
    del <- del[!duplicated(del$sus), ]
    if (at == 2) {
      dat$stats$transmat <- del
    } else {
      dat$stats$transmat <- rbind(dat$stats$transmat, del)
    }
  }
  dat$epi$si.flow[at] <- nInf
  
  #screen for colonization based on surveillance frequency
  freq = ifelse(is.numeric(dat$param$surveil.rate), dat$param$surveil.rate, dat$param$surveil.rate.dynamic)
  detected = NA
  isolation = NA
  decolonize = NA
  colonizedtime = NA
  if (at %% freq == 0) {
    #browser()
    
    #surveillance has occurred so update known status and record number of detected infants
    set1 = dat$attr$status[dat$attr$active==1]=="i"; set2 = dat$attr$status_known[dat$attr$active==1]=="i"
    detected = sum(set1==T & (set2==F | is.na(set2)), na.rm=T); rm(set1, set2)
    dat$attr$status_known[dat$attr$active==1] = dat$attr$status[dat$attr$active==1]
    
    #for dynamic surveillance, update surveillance rate: weekly when >=1 infant is detected, and continues each week until all infants in the NICU are screened negative; then the unit is surveilled once every three weeks until another MRSA colonization is detected
    dat$param$surveil.rate.dynamic = ifelse(detected>=1, at+168, at+504)
    
    #cohort colonized infants
    if (dat$param$cohort == TRUE) {
      isolation = length(dat$attr$location[dat$attr$active==1 & dat$attr$status=="i" & dat$attr$location!="isolation"])
      
      #per unit design, can isolate up to 4 infants
      if ((sum(dat$attr$location[dat$attr$active==1] == "isolation") + isolation) > 4) {
        
        #check if any infants can be isolated
        isolation_avail = 4 - sum(dat$attr$location[dat$attr$active==1] == "isolation")
        
        if (isolation_avail>0) {
          #isolate the first N infants
          dat$attr$location[dat$attr$active==1 & dat$attr$status=="i" & dat$attr$location!="isolation"][1:isolation_avail] = "isolation"
          isolation = isolation_avail
        } else {
          isolation = 0
        }
        
      } else {
        dat$attr$location[dat$attr$active==1 & dat$attr$status=="i" & dat$attr$location!="isolation"] = "isolation"
      }
      nw = set.vertex.attribute(nw, "location", dat$attr$location)
    }
    
    #attempt to decolonize based on decolon.eff; won't know if successful until next surveillance though
    if (dat$param$decolonize==T) {
      decolonize = rbinom(sum(dat$attr$active==1 & dat$attr$status=="i"), 1, dat$param$decolon.eff)
      
      #for infants who were colonized at simulation start,
      # we'll assume they were colonized at birth which is generally when admitted to the NICU
      colonizedtime = at - dat$attr$infTime[dat$attr$active==1 & dat$attr$status=="i"][decolonize==1]
      colonizedtime = ifelse(colonizedtime<at, colonizedtime, (at-1))
      
      #update status
      dat$attr$status[dat$attr$active==1 & dat$attr$status=="i"] = ifelse(decolonize==1, "s", "i")
      nw = set.vertex.attribute(nw, "status", dat$attr$status) ## SJ: this line not necessary
    }
    
  }
  dat$nw <- nw
  
  #record the surveillance stats at each time step for infants in the NICU (active==1)
  dat$epi$surveil.active[at] = sum(dat$attr$active==1)
  dat$epi$surveil.unknown.i[at] = sum(dat$attr$active==1 & dat$attr$status=="i")
  dat$epi$surveil.unknown.s[at] = sum(dat$attr$active==1 & dat$attr$status=="s")
  dat$epi$surveil.known.i[at] = sum(dat$attr$active==1 & dat$attr$status_known=="i", na.rm=T) #these two stats may not sum to infants in NICU
  dat$epi$surveil.known.s[at] = sum(dat$attr$active==1 & dat$attr$status_known=="s", na.rm=T) #because of admissions between surveillance periods
  dat$epi$surveil.detected[at] = detected
  dat$epi$surveil.decolon.success[at] = sum(decolonize==1)
  dat$epi$surveil.decolon.success.colonizedtime[at] = mean(colonizedtime)
  dat$epi$surveil.decolon.fail[at] = sum(decolonize==0)
  dat$epi$surveil.cohort[at] = isolation
  dat$epi$capacity.isolation[at] = ifelse((sum(dat$attr$location[dat$attr$active==1] == "isolation")==4), T, F)
  
  #record infection stats at each time step by location
  dat$epi$i.num.location.backhall[at] <- sum(dat$attr$active == 1 & dat$attr$location == "backhall" & dat$attr$status == "i")
  dat$epi$i.num.location.fronthall[at] <- sum(dat$attr$active == 1 & dat$attr$location == "fronthall" & dat$attr$status == "i")
  dat$epi$i.num.location.quietrm[at] <- sum(dat$attr$active == 1 & dat$attr$location == "quietrm" & dat$attr$status == "i")
  dat$epi$i.num.location.isolation[at] <- sum(dat$attr$active == 1 & dat$attr$location == "isolation" & dat$attr$status == "i")
  dat$epi$s.num.location.isolation[at] <- sum(dat$attr$active == 1 & dat$attr$location == "isolation" & dat$attr$status == "s")
  
  return(dat)
}


### PART 1: CALCULATE DEGREE DISTRIBUTION ###

#read data
load("network_prep.RData")

#census for denominator per day
census = NA

#tracks the overall number of interactions per hour per infant
total_interactions = NA

#tracks total edges on per infant
NICU$Network_edges_total = 0

#tracks the overall number of colonizations per day
total_ETcolonizations = NA
total_MRSAcolonizations = NA
NICU$Vent_start_date = NICU$Date_admission+NICU$Vent_start
NICU$Vent_end_date = NICU$Date_admission+NICU$Vent_start+NICU$Vent_length

#avg number of admissions and discharges per day
total_admit = NA
total_discharge = NA

#go through each day in the NICU and count degree distribution per hour per infant
for (i in 1:as.numeric(as.Date("2015-05-31")-as.Date("2015-01-01")))
{
  cat("\n\n************** ","Observation: ",i," **************\n",sep="")
  
  today = as.Date("2015-01-01")+i-1
  
  #get census as daily total since we don't have hourly
  todays_census = NICU$Census_admission[NICU$Date_admission==today][1]
  
  #impute missing census (no admissions that day) by averaging two days before and after
  if (is.na(todays_census))
    todays_census = round(mean(c(NICU$Census_admission[NICU$Date_admission==today-2][1], NICU$Census_admission[NICU$Date_admission==today-1][1], NICU$Census_admission[NICU$Date_admission==today+1][1], NICU$Census_admission[NICU$Date_admission==today+2][1]), na.rm=T))
  
  census = c(census, todays_census)
  
  #go through each hour
  for (j in 0:23)
  {
    hourly_interactions = na.omit(pt_interactions[pt_interactions$Date==today & pt_interactions$Hour==j, c("Personnel","Role","ID")])
    
    #found possible edges
    if (nrow(hourly_interactions)>1)
    {
      #get list of infants who were involved in an interaction this hour
      hourly_infants = unique(hourly_interactions$ID)
      
      #for each infant
      for (k in 1:length(hourly_infants))
      {
        #provider list for this infant
        provider_list = unique(hourly_interactions$Personnel[which(hourly_interactions$ID==hourly_infants[k])])
        
        #check if these providers have seen any other infants this hour (will include current infant), subtract one for the current infant
        provider_interactions = length(unique(hourly_interactions$ID[which(hourly_interactions$Personnel %in% provider_list)])) - 1
        
        #track total number of provider interactions
        total_interactions = c(total_interactions, nrow(hourly_interactions[hourly_interactions$ID==hourly_infants[k],]))
        
        #track total edges for this infant for mean degree by infant calculation
        NICU$Network_edges_total[NICU$ID==hourly_infants[k]] = NICU$Network_edges_total[NICU$ID==hourly_infants[k]] + provider_interactions
      } 
      
      #add infants that did not receive any care count for this hour
      total_interactions = c(total_interactions, rep(0,todays_census-length(hourly_infants)))
      
    } else {
      
      #add infants that did not receive any care count for this hour
      total_interactions = c(total_interactions, rep(0,todays_census))
      
    }
  }
  
  #track total ETT colonizations per day; since not all intubations have received a culture, need to artificially inflate by 50% (based on prediction of those with a culture, how often is it positive)
  #CrossTable(NICU$Vent_culture_positive, NICU$Vent_culture)
  total_ETcolonizations = c(total_ETcolonizations, sum(NICU$Vent_culture_positive[NICU$Vent_start_date<=today & NICU$Vent_end_date>=today], na.rm=T) + 0.5*sum(NICU$Vent[NICU$Vent_culture==0 & NICU$Vent_start_date<=today & NICU$Vent_end_date>=today], na.rm=T))
  
  #track total MRSA colonizations per day
  total_MRSAcolonizations = c(total_MRSAcolonizations, sum(NICU$MRSA_colonization[NICU$Date_admission<=today & NICU$Date_discharge_initial>=today], na.rm=T))
  
  #track total admit and discharges
  total_admit = c(total_admit,sum(NICU$Date_admission==today))
  total_discharge = c(total_discharge,sum(NICU$Date_discharge_initial==today))
  
}
rm(i,j,k,hourly_infants,provider_interactions,provider_list,today,todays_census,hourly_interactions)

#average number of edges per infant per hour
NICU$Network_edges_avg = NA

for (i in 1:nrow(NICU))
{
  cat("\n\n************** ","Observation: ",i," **************\n",sep="")
  
  #compute hours at risk for contact
  admitDate = ifelse(NICU$Date_admission[i]<as.Date("2015-01-01"), as.Date("2015-01-01"), NICU$Date_admission[i])
  dischargeDate = ifelse(NICU$Date_discharge_initial[i]>as.Date("2015-05-31"), as.Date("2015-05-31"), NICU$Date_discharge_initial[i])
  NICU$Network_edges_avg[i] = round(NICU$Network_edges_total[i] / ((dischargeDate-admitDate+1)*24), 0)
}
rm(i,admitDate,dischargeDate)

#save part 1
save.image("network_prep_degree.RData")


### PART 2: CALCULATE NETWORK STATS ###

#read data
load("network_prep_degree.RData")

#average number of edges per infant per hour in the NICU overall and by network attributes
mean_deg_overall = round(mean(NICU$Network_edges_avg, na.rm=T),1)
mean_deg_preterm = round(mean(NICU$Network_edges_avg[NICU$Preterm==1], na.rm=T),1)
mean_deg_vent = round(mean(NICU$Network_edges_avg[NICU$Vent==1], na.rm=T),1)
mean_deg_fronthall = round(mean(NICU$Network_edges_avg[NICU$Location_longest=="Location_201_209"], na.rm=T),1)
mean_deg_backhall = round(mean(NICU$Network_edges_avg[NICU$Location_longest=="Location_210_217"], na.rm=T),1)
mean_deg_quietrm = round(mean(NICU$Network_edges_avg[NICU$Location_longest=="Location_218_223"], na.rm=T),1)
mean_deg_isolation = round(mean(NICU$Network_edges_avg[NICU$Location_longest=="Location_224_225"], na.rm=T),1)

#distribution of edges per infant per hour in the NICU overall
table(NICU$Network_edges_avg, useNA="always")

#average network size (number of infants in the NICU on a given day)
network_size = round(mean(census, na.rm=T))

#number of hours to model 
#network_steps = median(NICU$LOS, na.rm=T)*24 #based on the median length of stay in the NICU
#network_steps = max(NICU$LOS,na.rm=T)*24 #based on max observed length of stay in the NICU
#network_steps = 91*24 #3 months
network_steps = 183*24 #6 months

#duration of at-risk can correspond to the average shift, in hours
network_duration = 12

#number of triangles on average for an hour
triangles = 2

#ratio of LOS by outcome
LOS_ETcolonized = mean(NICU$LOS[NICU$Vent_culture==1 & NICU$Vent_culture_positive==1],na.rm=T) / mean(NICU$LOS[NICU$Vent_culture==1 & NICU$Vent_culture_positive==0],na.rm=T)
LOS_MRSAcolonized = 1.922454 #computed from 2010-2015 NICU dataset: mean(NICU$LOS[NICU$MRSA_colonization==1 & NICU$Gestational_age<37 & NICU$Vent==0],na.rm=T) / mean(NICU$LOS[NICU$MRSA_colonization==0 & NICU$Gestational_age<37 & NICU$Vent==0],na.rm=T)

#mean degree distribution for the average network size
deg_distr = prop.table(table(NICU$Network_edges_avg))*network_size

#expected degree distribution
dpois(0:3, mean_deg_overall)*network_size

#degree distribution by network characteristics
describeBy(NICU$Network_edges_avg, NICU$Preterm)
describeBy(NICU$Network_edges_avg, NICU$Vent)

#what are the primary drivers of contact?
summary(lm(Network_edges_avg ~ Preterm + LBW + LOS + Cooling + Vent, data=NICU))


### PART 3: MODEL NETWORKS ###

#create a network of infants in the NICU
NICU_network = network.initialize(n=network_size, directed=F)
plot(NICU_network)

#edges: avg number of edges in the NICU for a given hour (multiply each degree by nodes with that degree), divided by two since the statistic is for number of edges (not number of nodes)
target_stats1_edges = round(sum(deg_distr*0:3)/2, 1)

#concurrent: avg number of infants with degree>=2 in the NICU for a given hour
target_stats1_concurrent = round(sum(deg_distr[3:4]), 1)

#degree(0): avg number of infants with degree=0 in the NICU for a given hour
target_stats1_deg0 = round(sum(deg_distr[1]), 1)

#degree(1): avg number of infants with degree=1 in the NICU for a given hour
target_stats1_deg1 = round(sum(deg_distr[2]), 1)

#degree(2): avg number of infants with degree=2 in the NICU for a given hour
target_stats1_deg2 = round(sum(deg_distr[3]), 1)

#degree(3): avg number of infants with degree=3 in the NICU for a given hour
target_stats1_deg3 = round(sum(deg_distr[4]), 1)

#avg number of edges by location for a given hour, even distribution among the three primary locations with no infants in isolation initially
NICU_network = set.vertex.attribute(NICU_network, attrname="location", value=c(rep("fronthall",18), rep("backhall",17), rep("quietrm",17)))
target_stats1_fronthall = as.numeric(round(mean_deg_fronthall*18, 1))
target_stats1_backhall = as.numeric(round(mean_deg_backhall*17, 1))
target_stats1_quietrm = as.numeric(round(mean_deg_quietrm*17, 1))
target_stats1_isolation = as.numeric(round(mean_deg_isolation*0, 1))

#average edges per location, assume 90% of care happens within location
target_stats1_location = round(target_stats1_edges*0.9)

#avg number of edges for a preterm infant for a given hour, computed by multiplying the mean degree of preterm by # of preterm infants
#set the intial values to ensure an even distribution by the 3 locations
#total distribution: CrossTable(NICU$Preterm)
NICU_network = set.vertex.attribute(NICU_network, attrname="preterm", value=c(rep("no",10),rep("yes",8),rep("no",9),rep("yes",8),rep("no",9),rep("yes",8)))
target_stats1_preterm = as.numeric(round(mean_deg_preterm*prop.table(table(NICU$Preterm))[2]*network_size, 1))

#avg number of edges for a ventilated infant for a given hour, computed by multiplying the mean degree of vent by # of vented infants
#set the intial values to ensure an even distribution by the 3 locations and by preterm
#total distribution: CrossTable(NICU$Preterm, NICU$Vent)
NICU_network = set.vertex.attribute(NICU_network, attrname="vent", value=c(rep("no",9),rep("yes",1),rep("no",6),rep("yes",2),rep("no",8),rep("yes",1),rep("no",6),rep("yes",2),rep("no",8),rep("yes",1),rep("no",6),rep("yes",2)))
target_stats1_vent = as.numeric(round(mean_deg_vent*prop.table(table(NICU$Vent))[2]*network_size, 1))

#average duration of edges in hrs
coef_diss1 = dissolution_coefs(dissolution = ~offset(edges), duration=network_duration)

#estimate the dynamic model
model1_dynamic = netest(nw=NICU_network, formation=~edges+concurrent+degree(1)+gwesp(0,fixed=T)+nodefactor("preterm")+nodefactor("vent")+nodematch("location"), target.stats=c(target_stats1_edges,target_stats1_concurrent,target_stats1_deg1,triangles,target_stats1_preterm,target_stats1_vent,target_stats1_location), coef.diss=coef_diss1, edapprox=T)
summary(model1_dynamic)

#simulate dynamic networks from model and diagnostics 
sim1_dynamic = netdx(model1_dynamic, nsteps=network_steps, nsims=20, ncores=4, nwstats.formula=~edges+concurrent+degree(0:3)+gwesp(0,fixed=T)+nodefactor("preterm")+nodefactor("vent")+nodematch("location"))
sim1_dynamic

#output to tif for publication 
#tiff("Figure1_supplement.tif",height=6,width=10,units='in',res=1200) 
plot(sim1_dynamic)
#dev.off() 

#save ergm
save.image("network_ergm.RData")


### PART 6: MODEL EPIDEMIC ###

#read data
load("network_ergm.RData")

#set colonization assumptions and infection parameters
ADT_admit = round(mean(total_admit,na.rm=T)/24,4) #average admission per hour
ADT_disch = round(mean(total_admit/census,na.rm=T)/24,4) #average discharge per day (set as admission rate to balance network size), computed as rate per person per hour
ADT_colon =  round(mean(total_admit/census,na.rm=T)/24 * 1/LOS_MRSAcolonized,4) #average discharge rate per hr if colonized, computed by ratio of LOS
inf_prob = 0.15*0.05 #probabilty of colonization per provider interaction
birth_prob = 0.025 #probability of colonization at birth from MRSA colonized mom
#n_colon = round(network_size*birth_prob) #number of infants initially MRSA colonized
n_colon = 0 #assume no initially colonized infants based on the historic mode
hygiene_eff = 0.87 #effectiveness computed as product of compliance and efficacy
surveil_time = "dynamic" #surveil for MRSA colonization every XX hours, where XX is "dynamic"=current practice, 168=every week, 336=every 2 weeks, 504=every 3 weeks, 672=ever 4 weeks
surveil_time_dynamic = 504 #if surveil time is dynamic, when first surveillance should occur
decolon_eff = 0.56 #effectiveness of decolonization, intranasal mupirocin + chlorhexidine gluconate washing
n_sims = 1 #number of simulations

#simulate network attributes
#mrsa_sim_location = netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=hygiene_eff, birth.prob=birth_prob, surveil.rate=surveil_time, surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=n_sims, ncores=4, births.FUN=admit.net, infection.FUN=surveil.net))

#analyses
rm(list = ls())
gc()
#load("network_ergm2.RData")
load("network_ergm2.RData")

#surveil: dynamic hrs; hygiene: 87%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.87, birth.prob=birth_prob, surveil.rate="dynamic", surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_dynamic_87 = tmp
    } else {
      mrsa_sim_dynamic_87 = merge(mrsa_sim_dynamic_87, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_dynamic_87.RData")
save.image("mrsa_sim_dynamic_87.RData")
rm(list = ls())
gc()
load("network_ergm2.RData")

#surveil: 168 hrs; hygiene: 87%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.87, birth.prob=birth_prob, surveil.rate=168, surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_168_87 = tmp
    } else {
      mrsa_sim_168_87 = merge(mrsa_sim_168_87, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_168_87.RData")
rm(list = ls())
gc()
load("network_ergm2.RData")

#surveil: 336 hrs; hygiene: 87%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.87, birth.prob=birth_prob, surveil.rate=336, surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_336_87 = tmp
    } else {
      mrsa_sim_336_87 = merge(mrsa_sim_336_87, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_336_87.RData")
rm(list = ls())
gc()
load("network_ergm2.RData")

#surveil: 504 hrs; hygiene: 87%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.87, birth.prob=birth_prob, surveil.rate=504, surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_504_87 = tmp
    } else {
      mrsa_sim_504_87 = merge(mrsa_sim_504_87, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_504_87.RData")
rm(list = ls())
gc()
load("network_ergm2.RData")


#surveil: 672 hrs; hygiene: 87%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.87, birth.prob=birth_prob, surveil.rate=672, surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_672_87 = tmp
    } else {
      mrsa_sim_672_87 = merge(mrsa_sim_672_87, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_672_87.RData")
rm(list = ls())
gc()
load("network_ergm2.RData")

#surveil: dynamic hrs; hygiene: 54%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.54, birth.prob=birth_prob, surveil.rate="dynamic", surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_dynamic_54 = tmp
    } else {
      mrsa_sim_dynamic_54 = merge(mrsa_sim_dynamic_54, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_dynamic_54.RData")
rm(list = ls())
gc()
load("network_ergm2.RData")

#surveil: 168 hrs; hygiene: 54%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.54, birth.prob=birth_prob, surveil.rate=168, surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_168_54 = tmp
    } else {
      mrsa_sim_168_54 = merge(mrsa_sim_168_54, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_168_54.RData")
rm(list = ls())
gc()
load("network_ergm2.RData")

#surveil: 336 hrs; hygiene: 54%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.54, birth.prob=birth_prob, surveil.rate=336, surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_336_54 = tmp
    } else {
      mrsa_sim_336_54 = merge(mrsa_sim_336_54, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_336_54.RData")
rm(list = ls())
gc()
load("network_ergm2.RData")

#surveil: 504 hrs; hygiene: 54%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.54, birth.prob=birth_prob, surveil.rate=504, surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_504_54 = tmp
    } else {
      mrsa_sim_504_54 = merge(mrsa_sim_504_54, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_504_54.RData")
rm(list = ls())
gc()
load("network_ergm2.RData")

#surveil: 672 hrs; hygiene: 54%
n_tries=0
n_success=0
while(n_success<100)
{
  cat("\n\n************** ","n_tries: ",n_tries,"; n_success: ",n_success," **************\n",sep="")
  
  tmp = tryCatch(netsim(model1_dynamic, param.net(inf.prob=inf_prob, act.rate=mean_deg_overall, b.rate=ADT_admit, ds.rate=ADT_disch, di.rate=ADT_colon, inter.eff=0.54, birth.prob=birth_prob, surveil.rate=672, surveil.rate.dynamic=surveil_time_dynamic, decolon.eff=decolon_eff, decolonize=T, cohort=T), init.net(i.num=n_colon, status.rand=F), control.net(type = "SI", nsteps=network_steps, nsims=1, ncores=4, verbose=F, births.FUN=admit.net, infection.FUN=surveil.net)), error=function(e) NA)
  
  if (is.list(tmp))
  {
    n_success = n_success + 1
    
    if (n_success==1){
      mrsa_sim_672_54 = tmp
    } else {
      mrsa_sim_672_54 = merge(mrsa_sim_672_54, tmp, param.error=F)
    }
  }
  n_tries = n_tries + 1
  
  rm(tmp)
  gc()
}
rm(n_tries,n_success)

save.image("mrsa_sim_672_54.RData")


# ### AGGREGATE DATA for ANALYSES ##
# 
# mrsa_sim = data.frame("surveil"=NA,
#                       "hygiene"=NA,
#                       "timestep"=NA,
#                       "b.flow"=NA,
#                       "bs.flow"=NA,
#                       "bi.flow"=NA,
#                       "ds.flow"=NA,
#                       "di.flow"=NA,
#                       "i.num.location.isolation"=NA,
#                       "s.num.location.isolation"=NA,
#                       "capacity.nicu"=NA,
#                       "capacity.isolation"=NA,
#                       "surveil.active"=NA,
#                       "surveil.unknown.i"=NA,
#                       "surveil.unknown.s"=NA,
#                       "surveil.known.i"=NA,
#                       "surveil.known.s"=NA,
#                       "surveil.detected"=NA,
#                       "surveil.decolon.success"=NA,
#                       "surveil.decolon.success.colonizedtime"=NA,
#                       "surveil.decolon.fail"=NA,
#                       "surveil.cohort"=NA,
#                       "surveil.cohort.prop"=NA, stringsAsFactors=F)
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_dynamic_87.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep("dynamic",network_steps),
#                                       "hygiene"=rep(87,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_dynamic_87$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_dynamic_87$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_dynamic_87$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_dynamic_87$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_dynamic_87$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_dynamic_87$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_dynamic_87$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_dynamic_87$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_dynamic_87$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_dynamic_87$epi$surveil.cohort/mrsa_sim_dynamic_87$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_168_87.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep(168,network_steps),
#                                       "hygiene"=rep(87,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_168_87$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_168_87$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_168_87$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_168_87$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_168_87$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_168_87$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_168_87$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_168_87$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_168_87$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_168_87$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_168_87$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_168_87$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_168_87$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_168_87$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_168_87$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_168_87$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_168_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_168_87$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_168_87$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_168_87$epi$surveil.cohort/mrsa_sim_168_87$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_336_87.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep(336,network_steps),
#                                       "hygiene"=rep(87,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_336_87$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_336_87$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_336_87$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_336_87$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_336_87$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_336_87$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_336_87$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_336_87$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_336_87$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_336_87$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_336_87$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_336_87$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_336_87$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_336_87$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_336_87$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_336_87$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_336_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_336_87$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_336_87$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_336_87$epi$surveil.cohort/mrsa_sim_336_87$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_504_87.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep(504,network_steps),
#                                       "hygiene"=rep(87,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_504_87$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_504_87$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_504_87$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_504_87$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_504_87$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_504_87$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_504_87$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_504_87$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_504_87$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_504_87$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_504_87$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_504_87$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_504_87$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_504_87$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_504_87$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_504_87$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_504_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_504_87$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_504_87$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_504_87$epi$surveil.cohort/mrsa_sim_504_87$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_672_87.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep(672,network_steps),
#                                       "hygiene"=rep(87,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_672_87$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_672_87$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_672_87$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_672_87$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_672_87$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_672_87$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_672_87$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_672_87$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_672_87$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_672_87$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_672_87$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_672_87$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_672_87$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_672_87$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_672_87$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_672_87$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_672_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_672_87$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_672_87$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_672_87$epi$surveil.cohort/mrsa_sim_672_87$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_dynamic_54.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep("dynamic",network_steps),
#                                       "hygiene"=rep(54,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_dynamic_54$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_dynamic_54$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_dynamic_54$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_dynamic_54$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_dynamic_54$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_dynamic_54$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_dynamic_54$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_dynamic_54$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_dynamic_54$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_dynamic_54$epi$surveil.cohort/mrsa_sim_dynamic_54$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_168_54.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep(168,network_steps),
#                                       "hygiene"=rep(54,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_168_54$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_168_54$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_168_54$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_168_54$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_168_54$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_168_54$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_168_54$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_168_54$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_168_54$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_168_54$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_168_54$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_168_54$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_168_54$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_168_54$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_168_54$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_168_54$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_168_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_168_54$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_168_54$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_168_54$epi$surveil.cohort/mrsa_sim_168_54$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_336_54.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep(336,network_steps),
#                                       "hygiene"=rep(54,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_336_54$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_336_54$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_336_54$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_336_54$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_336_54$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_336_54$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_336_54$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_336_54$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_336_54$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_336_54$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_336_54$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_336_54$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_336_54$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_336_54$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_336_54$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_336_54$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_336_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_336_54$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_336_54$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_336_54$epi$surveil.cohort/mrsa_sim_336_54$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_504_54.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep(504,network_steps),
#                                       "hygiene"=rep(54,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_504_54$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_504_54$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_504_54$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_504_54$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_504_54$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_504_54$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_504_54$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_504_54$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_504_54$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_504_54$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_504_54$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_504_54$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_504_54$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_504_54$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_504_54$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_504_54$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_504_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_504_54$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_504_54$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_504_54$epi$surveil.cohort/mrsa_sim_504_54$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# load("mrsa_sim_672_54.RData")
# mrsa_sim = rbind(mrsa_sim, data.frame("surveil"=rep(672,network_steps),
#                                       "hygiene"=rep(54,network_steps),
#                                       "timestep"=1:network_steps,
#                                       "b.flow"=rowMeans(mrsa_sim_672_54$epi$b.flow),
#                                       "bs.flow"=rowMeans(mrsa_sim_672_54$epi$bs.flow),
#                                       "bi.flow"=rowMeans(mrsa_sim_672_54$epi$bi.flow),
#                                       "ds.flow"=rowMeans(mrsa_sim_672_54$epi$ds.flow),
#                                       "di.flow"=rowMeans(mrsa_sim_672_54$epi$di.flow),
#                                       "i.num.location.isolation"=rowMeans(mrsa_sim_672_54$epi$i.num.location.isolation),
#                                       "s.num.location.isolation"=rowMeans(mrsa_sim_672_54$epi$s.num.location.isolation),
#                                       "capacity.nicu"=rowSums(mrsa_sim_672_54$epi$capacity.nicu),
#                                       "capacity.isolation"=rowSums(mrsa_sim_672_54$epi$capacity.isolation),
#                                       "surveil.active"=rowMeans(mrsa_sim_672_54$epi$surveil.active),
#                                       "surveil.unknown.i"=rowMeans(mrsa_sim_672_54$epi$surveil.unknown.i),
#                                       "surveil.unknown.s"=rowMeans(mrsa_sim_672_54$epi$surveil.unknown.s),
#                                       "surveil.known.i"=rowMeans(mrsa_sim_672_54$epi$surveil.known.i),
#                                       "surveil.known.s"=rowMeans(mrsa_sim_672_54$epi$surveil.known.s),
#                                       "surveil.detected"=rowMeans(mrsa_sim_672_54$epi$surveil.detected, na.rm=T),
#                                       "surveil.decolon.success"=rowMeans(mrsa_sim_672_54$epi$surveil.decolon.success, na.rm=T),
#                                       "surveil.decolon.success.colonizedtime"=rowMeans(mrsa_sim_672_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),
#                                       "surveil.decolon.fail"=rowMeans(mrsa_sim_672_54$epi$surveil.decolon.fail, na.rm=T),
#                                       "surveil.cohort"=rowMeans(mrsa_sim_672_54$epi$surveil.cohort, na.rm=T),
#                                       "surveil.cohort.prop"=rowMeans(mrsa_sim_672_54$epi$surveil.cohort/mrsa_sim_672_54$epi$surveil.known.i, na.rm=T), stringsAsFactors=F))
# 
# rm(list = ls()[-which(ls()=="mrsa_sim")]); gc();
# mrsa_sim = mrsa_sim[-1, ]
# save.image("mrsa_sim_results.RData")
# 
# 
# ### ANALYSES ###
# 
# mrsa_sim_location$epi$b.flow
# mrsa_sim_location$epi$bs.flow
# mrsa_sim_location$epi$bi.flow
# mrsa_sim_location$epi$ds.flow
# mrsa_sim_location$epi$di.flow
# mrsa_sim_location$epi$capacity.nicu
# mrsa_sim_location$epi$capacity.isolation
# 
# #surveillance data
# mrsa_sim_location$epi$surveil.active
# mrsa_sim_location$epi$surveil.unknown.i
# mrsa_sim_location$epi$surveil.unknown.s
# mrsa_sim_location$epi$surveil.known.i
# mrsa_sim_location$epi$surveil.known.s
# mrsa_sim_location$epi$surveil.detected
# mrsa_sim_location$epi$surveil.decolon.success
# mrsa_sim_location$epi$surveil.decolon.success.colonizedtime
# mrsa_sim_location$epi$surveil.decolon.fail
# mrsa_sim_location$epi$surveil.cohort
# 
# #analytic plots
# mrsa_sim_location
# plot(mrsa_sim_location)
# plot(mrsa_sim_location, sim.lines = TRUE, mean.line = FALSE, qnts = FALSE, popfrac = FALSE)
# plot(mrsa_sim_location, mean.smooth = FALSE, qnts = 1, qnts.smooth = FALSE, popfrac = FALSE)
# 
# #flow size corresponds to the flow between infection and recovery, "si" shows incidence
# plot(mrsa_sim_location, y = c("si.flow"), qnts = FALSE, leg = TRUE, main = "Flow Sizes")
# 
# #plot overall prevalance
# plot(mrsa_sim_location, y = "i.num", qnts = 1, mean.col = "steelblue", qnts.col = "steelblue", main = "Total Prevalence")
# 
# #plot location specific prevalance
# plot(mrsa_sim_location, y=c("i.num.location.fronthall", "i.num.location.backhall", "i.num.location.quietrm", "i.num.location.isolation"), mean.col=c("red","green","blue","black"), qnts=0.95, legend=T, main="MRSA Colonization by Location")
# 
# #obtain simulation data
# mrsa_sim_location_data = as.data.frame(mrsa_sim_location, out="vals", sim=1)
# for (i in 1:(n_sims-1)) {
#   mrsa_sim_location_data = rbind(mrsa_sim_location_data, as.data.frame(mrsa_sim_location, out = "vals", sim=(i+1)))
# }
# mrsa_sim_location_data$sim = rep(1:n_sims,network_steps)[order(rep(1:n_sims,network_steps))]
# 
# # you can use ggplot here too, if you'd like
# 
# library(ggplot2)
# ggplot(df, aes(x = time)) +
#   geom_line(aes(y = i.num, group = sim))


### PLOTS for PAPER ###

load("mrsa_sim_672_87.RData")
y_672 = rowMeans(mrsa_sim_672_87$epi$surveil.known.i)
rm(list = ls()[-which(ls() %in% c("y_672"))]); gc();

load("mrsa_sim_504_87.RData")
y_504 = rowMeans(mrsa_sim_504_87$epi$surveil.known.i)
rm(list = ls()[-which(ls() %in% c("y_672","y_504"))]); gc();

load("mrsa_sim_336_87.RData")
y_336 = rowMeans(mrsa_sim_336_87$epi$surveil.known.i)
rm(list = ls()[-which(ls() %in% c("y_672","y_504","y_336"))]); gc();

load("mrsa_sim_168_87.RData")
y_168 = rowMeans(mrsa_sim_168_87$epi$surveil.known.i)
rm(list = ls()[-which(ls() %in% c("y_672","y_504","y_336","y_168"))]); gc();

load("mrsa_sim_dynamic_87.RData")
y_dynamic = rowMeans(mrsa_sim_dynamic_87$epi$surveil.known.i)

#averaged plots, MRSA colonization @ 87% effectiveness
tiff("Figure1a.tif",height=4,width=6,units='in',res=1200)
plot(x=1:network_steps, y=y_672, type="l", xlab="Timestep in Hrs.", ylab="No. MRSA colonized infants", lwd=3, lty=1, col=brewer.pal(4,"Greys")[1])
lines(x=1:network_steps, y=y_504, lwd=3, lty=1, col=brewer.pal(4,"Greys")[2])
lines(x=1:network_steps, y=y_336, lwd=3, lty=1, col=brewer.pal(4,"Greys")[3])
lines(x=1:network_steps, y=y_168, lwd=3, lty=1, col=brewer.pal(4,"Greys")[4])
lines(x=1:network_steps, y=y_dynamic, lwd=5, lty=1, col="#000000")
legend("topleft", lty=rep(1,5), lwd=c(rep(3,4),5), col=c(brewer.pal(4,"Greys"),"#000000"), c("672 hrs.","504 hrs.","336 hrs.","168 hrs.","dynamic"), cex=0.7)
dev.off()

#individual dynamic simulation plots, MRSA colonization @ 87% effectiveness
tiff("Figure1b.tif",height=4,width=6,units='in',res=1200)
plot(x=1:network_steps, y=mrsa_sim_dynamic_87$epi$surveil.known.i[,5], type="l", ylim=c(0,4), xlab="Timestep in Hrs.", ylab="No. MRSA colonized infants", lwd=3, lty=1, col=brewer.pal(3,"Greys")[1])
lines(x=1:network_steps, y=mrsa_sim_dynamic_87$epi$surveil.known.i[,10], lwd=3, lty=1, col=brewer.pal(4,"Greys")[2])
lines(x=1:network_steps, y=mrsa_sim_dynamic_87$epi$surveil.known.i[,75], lwd=3, lty=1, col="#000000")
legend("topleft", lty=rep(1,5), lwd=c(rep(3,4),5), col=c(brewer.pal(3,"Greys")[1:2],"#000000"), c("simulation #5","simulation #10", "simulation #75"), cex=0.7)
dev.off()

load("mrsa_sim_672_54.RData")
y_672 = rowMeans(mrsa_sim_672_54$epi$surveil.known.i)
rm(list = ls()[-which(ls() %in% c("y_672"))]); gc();

load("mrsa_sim_504_54.RData")
y_504 = rowMeans(mrsa_sim_504_54$epi$surveil.known.i)
rm(list = ls()[-which(ls() %in% c("y_672","y_504"))]); gc();

load("mrsa_sim_336_54.RData")
y_336 = rowMeans(mrsa_sim_336_54$epi$surveil.known.i)
rm(list = ls()[-which(ls() %in% c("y_672","y_504","y_336"))]); gc();

load("mrsa_sim_168_54.RData")
y_168 = rowMeans(mrsa_sim_168_54$epi$surveil.known.i)
rm(list = ls()[-which(ls() %in% c("y_672","y_504","y_336","y_168"))]); gc();

load("mrsa_sim_dynamic_54.RData")
y_dynamic = rowMeans(mrsa_sim_dynamic_54$epi$surveil.known.i)

#averaged plots, MRSA colonization @ 54% effectiveness
tiff("Figure2.tif",height=4,width=6,units='in',res=1200)
plot(x=1:network_steps, y=y_672, type="l", xlab="Timestep in Hrs.", ylab="No. MRSA colonized infants", lwd=3, lty=1, col=brewer.pal(4,"Greys")[1])
lines(x=1:network_steps, y=y_504, lwd=3, lty=1, col=brewer.pal(4,"Greys")[2])
lines(x=1:network_steps, y=y_336, lwd=3, lty=1, col=brewer.pal(4,"Greys")[3])
lines(x=1:network_steps, y=y_168, lwd=3, lty=1, col=brewer.pal(4,"Greys")[4])
lines(x=1:network_steps, y=y_dynamic, lwd=5, lty=1, col="#000000")
legend("topleft", lty=rep(1,5), lwd=c(rep(3,4),5), col=c(brewer.pal(4,"Greys"),"#000000"), c("672 hrs.","504 hrs.","336 hrs.","168 hrs.","dynamic"), cex=0.7)
dev.off()


### ANALYSIS for PAPER ###

#general stats from dynamic program
# mrsa_sim$surveil.unknown.i[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87 & mrsa_sim$timestep==2]
# mrsa_sim$surveil.unknown.i[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87 & mrsa_sim$timestep==4392]
# mean(mrsa_sim$surveil.unknown.i[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T)
# mean(mrsa_sim$surveil.unknown.i[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T)/mean(mrsa_sim$surveil.active[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T)

load("mrsa_sim_dynamic_87.RData")
mean(colSums(mrsa_sim_dynamic_87$epi$surveil.unknown.i[2,], na.rm=T), na.rm=T)
mean(colSums(mrsa_sim_dynamic_87$epi$surveil.unknown.i[4392,], na.rm=T), na.rm=T)
mean(colSums(mrsa_sim_dynamic_87$epi$surveil.unknown.i, na.rm=T), na.rm=T) / network_steps
mean(colSums(mrsa_sim_dynamic_87$epi$surveil.unknown.i, na.rm=T), na.rm=T) / mean(colSums(mrsa_sim_dynamic_87$epi$surveil.active, na.rm=T), na.rm=T)

# #indicators for table, 87%
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]))
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87]))
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87]))
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87]))
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87]))
# 
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# 
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]))
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]))
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]))
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]))
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]))
# 
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87]), probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87]), probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87]), probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87]), probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87]), probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==168 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==336 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==504 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==672 & mrsa_sim$hygiene==87], probs=c(0.025,0.975), na.rm=T)
# 
# #indicators for table, 54%
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]))
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54]))
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54]))
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54]))
# sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54]))
# 
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.active[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.active[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# 
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]))
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]))
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]))
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]))
# sum(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.detected[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T) * sum(!is.na(mrsa_sim$surveil.detected[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]))
# 
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54]), probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54]), probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54]), probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54]), probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54]), na.rm=T); quantile(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54]/(mrsa_sim$surveil.decolon.success[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54] + mrsa_sim$surveil.decolon.fail[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54]), probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.decolon.success.colonizedtime[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$i.num.location.isolation[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$s.num.location.isolation[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# 
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil=="dynamic" & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==168 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==336 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==504 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)
# mean(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], na.rm=T); quantile(mrsa_sim$surveil.cohort.prop[mrsa_sim$surveil==672 & mrsa_sim$hygiene==54], probs=c(0.025,0.975), na.rm=T)

#indicators for table: dynamic surveillance, 87% hygiene
load("mrsa_sim_dynamic_87.RData")

sum(!is.na(mrsa_sim_dynamic_87$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_87$epi$surveil.detected)

mean(colSums(mrsa_sim_dynamic_87$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_dynamic_87$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_dynamic_87$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_87$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_dynamic_87$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_87$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_87$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_dynamic_87$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_dynamic_87$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_dynamic_87$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_dynamic_87$epi$surveil.decolon.success / (mrsa_sim_dynamic_87$epi$surveil.decolon.success+mrsa_sim_dynamic_87$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_dynamic_87$epi$surveil.decolon.success / (mrsa_sim_dynamic_87$epi$surveil.decolon.success+mrsa_sim_dynamic_87$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_87$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_dynamic_87$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_87$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_87$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_dynamic_87$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_87$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_dynamic_87$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_87$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_87$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_dynamic_87$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_87$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_dynamic_87$epi$surveil.cohort/mrsa_sim_dynamic_87$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_dynamic_87$epi$surveil.cohort/mrsa_sim_dynamic_87$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))

#indicators for table: 168 surveillance, 87% hygiene
load("mrsa_sim_168_87.RData")

sum(!is.na(mrsa_sim_168_87$epi$surveil.detected)) / ncol(mrsa_sim_168_87$epi$surveil.detected)

mean(colSums(mrsa_sim_168_87$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_168_87$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_168_87$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_168_87$epi$surveil.detected)) / ncol(mrsa_sim_168_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_168_87$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_168_87$epi$surveil.detected)) / ncol(mrsa_sim_168_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_87$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_168_87$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_168_87$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_168_87$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_168_87$epi$surveil.decolon.success / (mrsa_sim_168_87$epi$surveil.decolon.success+mrsa_sim_168_87$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_168_87$epi$surveil.decolon.success / (mrsa_sim_168_87$epi$surveil.decolon.success+mrsa_sim_168_87$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_168_87$epi$surveil.detected)) / ncol(mrsa_sim_168_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_168_87$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_168_87$epi$surveil.detected)) / ncol(mrsa_sim_168_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_87$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_168_87$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_87$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_168_87$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_87$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_168_87$epi$surveil.detected)) / ncol(mrsa_sim_168_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_168_87$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_168_87$epi$surveil.detected)) / ncol(mrsa_sim_168_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_168_87$epi$surveil.cohort/mrsa_sim_168_87$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_168_87$epi$surveil.cohort/mrsa_sim_168_87$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))

#indicators for table: 336 surveillance, 87% hygiene
load("mrsa_sim_336_87.RData")

sum(!is.na(mrsa_sim_336_87$epi$surveil.detected)) / ncol(mrsa_sim_336_87$epi$surveil.detected)

mean(colSums(mrsa_sim_336_87$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_336_87$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_336_87$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_336_87$epi$surveil.detected)) / ncol(mrsa_sim_336_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_336_87$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_336_87$epi$surveil.detected)) / ncol(mrsa_sim_336_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_87$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_336_87$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_336_87$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_336_87$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_336_87$epi$surveil.decolon.success / (mrsa_sim_336_87$epi$surveil.decolon.success+mrsa_sim_336_87$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_336_87$epi$surveil.decolon.success / (mrsa_sim_336_87$epi$surveil.decolon.success+mrsa_sim_336_87$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_336_87$epi$surveil.detected)) / ncol(mrsa_sim_336_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_336_87$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_336_87$epi$surveil.detected)) / ncol(mrsa_sim_336_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_87$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_336_87$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_87$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_336_87$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_87$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_336_87$epi$surveil.detected)) / ncol(mrsa_sim_336_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_336_87$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_336_87$epi$surveil.detected)) / ncol(mrsa_sim_336_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_336_87$epi$surveil.cohort/mrsa_sim_336_87$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_336_87$epi$surveil.cohort/mrsa_sim_336_87$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))

#indicators for table: 504 surveillance, 87% hygiene
load("mrsa_sim_504_87.RData")

sum(!is.na(mrsa_sim_504_87$epi$surveil.detected)) / ncol(mrsa_sim_504_87$epi$surveil.detected)

mean(colSums(mrsa_sim_504_87$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_504_87$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_504_87$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_504_87$epi$surveil.detected)) / ncol(mrsa_sim_504_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_504_87$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_504_87$epi$surveil.detected)) / ncol(mrsa_sim_504_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_87$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_504_87$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_504_87$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_504_87$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_504_87$epi$surveil.decolon.success / (mrsa_sim_504_87$epi$surveil.decolon.success+mrsa_sim_504_87$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_504_87$epi$surveil.decolon.success / (mrsa_sim_504_87$epi$surveil.decolon.success+mrsa_sim_504_87$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_504_87$epi$surveil.detected)) / ncol(mrsa_sim_504_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_504_87$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_504_87$epi$surveil.detected)) / ncol(mrsa_sim_504_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_87$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_504_87$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_87$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_504_87$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_87$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_504_87$epi$surveil.detected)) / ncol(mrsa_sim_504_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_504_87$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_504_87$epi$surveil.detected)) / ncol(mrsa_sim_504_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_504_87$epi$surveil.cohort/mrsa_sim_504_87$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_504_87$epi$surveil.cohort/mrsa_sim_504_87$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))

#indicators for table: 672 surveillance, 87% hygiene
load("mrsa_sim_672_87.RData")

sum(!is.na(mrsa_sim_672_87$epi$surveil.detected)) / ncol(mrsa_sim_672_87$epi$surveil.detected)

mean(colSums(mrsa_sim_672_87$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_672_87$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_672_87$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_672_87$epi$surveil.detected)) / ncol(mrsa_sim_672_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_672_87$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_672_87$epi$surveil.detected)) / ncol(mrsa_sim_672_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_87$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_672_87$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_672_87$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_672_87$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_672_87$epi$surveil.decolon.success / (mrsa_sim_672_87$epi$surveil.decolon.success+mrsa_sim_672_87$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_672_87$epi$surveil.decolon.success / (mrsa_sim_672_87$epi$surveil.decolon.success+mrsa_sim_672_87$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_87$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_672_87$epi$surveil.detected)) / ncol(mrsa_sim_672_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_672_87$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_672_87$epi$surveil.detected)) / ncol(mrsa_sim_672_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_87$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_672_87$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_87$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_672_87$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_87$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_672_87$epi$surveil.detected)) / ncol(mrsa_sim_672_87$epi$surveil.detected))
quantile(colSums(mrsa_sim_672_87$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_672_87$epi$surveil.detected)) / ncol(mrsa_sim_672_87$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_672_87$epi$surveil.cohort/mrsa_sim_672_87$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_672_87$epi$surveil.cohort/mrsa_sim_672_87$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))

#indicators for table: dynamic surveillance, 54% hygiene
load("mrsa_sim_dynamic_54.RData")

sum(!is.na(mrsa_sim_dynamic_54$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_54$epi$surveil.detected)

mean(colSums(mrsa_sim_dynamic_54$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_dynamic_54$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_dynamic_54$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_54$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_dynamic_54$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_54$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_54$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_dynamic_54$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_dynamic_54$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_dynamic_54$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_dynamic_54$epi$surveil.decolon.success / (mrsa_sim_dynamic_54$epi$surveil.decolon.success+mrsa_sim_dynamic_54$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_dynamic_54$epi$surveil.decolon.success / (mrsa_sim_dynamic_54$epi$surveil.decolon.success+mrsa_sim_dynamic_54$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_54$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_dynamic_54$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_54$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_54$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_dynamic_54$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_54$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_dynamic_54$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_dynamic_54$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_54$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_dynamic_54$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_dynamic_54$epi$surveil.detected)) / ncol(mrsa_sim_dynamic_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_dynamic_54$epi$surveil.cohort/mrsa_sim_dynamic_54$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_dynamic_54$epi$surveil.cohort/mrsa_sim_dynamic_54$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))

#indicators for table: 168 surveillance, 54% hygiene
load("mrsa_sim_168_54.RData")

sum(!is.na(mrsa_sim_168_54$epi$surveil.detected)) / ncol(mrsa_sim_168_54$epi$surveil.detected)

mean(colSums(mrsa_sim_168_54$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_168_54$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_168_54$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_168_54$epi$surveil.detected)) / ncol(mrsa_sim_168_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_168_54$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_168_54$epi$surveil.detected)) / ncol(mrsa_sim_168_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_54$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_168_54$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_168_54$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_168_54$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_168_54$epi$surveil.decolon.success / (mrsa_sim_168_54$epi$surveil.decolon.success+mrsa_sim_168_54$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_168_54$epi$surveil.decolon.success / (mrsa_sim_168_54$epi$surveil.decolon.success+mrsa_sim_168_54$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_168_54$epi$surveil.detected)) / ncol(mrsa_sim_168_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_168_54$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_168_54$epi$surveil.detected)) / ncol(mrsa_sim_168_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_54$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_168_54$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_54$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_168_54$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_168_54$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_168_54$epi$surveil.detected)) / ncol(mrsa_sim_168_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_168_54$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_168_54$epi$surveil.detected)) / ncol(mrsa_sim_168_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_168_54$epi$surveil.cohort/mrsa_sim_168_54$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_168_54$epi$surveil.cohort/mrsa_sim_168_54$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))

#indicators for table: 336 surveillance, 54% hygiene
load("mrsa_sim_336_54.RData")

sum(!is.na(mrsa_sim_336_54$epi$surveil.detected)) / ncol(mrsa_sim_336_54$epi$surveil.detected)

mean(colSums(mrsa_sim_336_54$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_336_54$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_336_54$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_336_54$epi$surveil.detected)) / ncol(mrsa_sim_336_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_336_54$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_336_54$epi$surveil.detected)) / ncol(mrsa_sim_336_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_54$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_336_54$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_336_54$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_336_54$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_336_54$epi$surveil.decolon.success / (mrsa_sim_336_54$epi$surveil.decolon.success+mrsa_sim_336_54$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_336_54$epi$surveil.decolon.success / (mrsa_sim_336_54$epi$surveil.decolon.success+mrsa_sim_336_54$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_336_54$epi$surveil.detected)) / ncol(mrsa_sim_336_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_336_54$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_336_54$epi$surveil.detected)) / ncol(mrsa_sim_336_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_54$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_336_54$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_54$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_336_54$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_336_54$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_336_54$epi$surveil.detected)) / ncol(mrsa_sim_336_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_336_54$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_336_54$epi$surveil.detected)) / ncol(mrsa_sim_336_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_336_54$epi$surveil.cohort/mrsa_sim_336_54$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_336_54$epi$surveil.cohort/mrsa_sim_336_54$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))

#indicators for table: 504 surveillance, 54% hygiene
load("mrsa_sim_504_54.RData")

sum(!is.na(mrsa_sim_504_54$epi$surveil.detected)) / ncol(mrsa_sim_504_54$epi$surveil.detected)

mean(colSums(mrsa_sim_504_54$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_504_54$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_504_54$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_504_54$epi$surveil.detected)) / ncol(mrsa_sim_504_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_504_54$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_504_54$epi$surveil.detected)) / ncol(mrsa_sim_504_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_54$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_504_54$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_504_54$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_504_54$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_504_54$epi$surveil.decolon.success / (mrsa_sim_504_54$epi$surveil.decolon.success+mrsa_sim_504_54$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_504_54$epi$surveil.decolon.success / (mrsa_sim_504_54$epi$surveil.decolon.success+mrsa_sim_504_54$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_504_54$epi$surveil.detected)) / ncol(mrsa_sim_504_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_504_54$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_504_54$epi$surveil.detected)) / ncol(mrsa_sim_504_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_54$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_504_54$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_54$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_504_54$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_504_54$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_504_54$epi$surveil.detected)) / ncol(mrsa_sim_504_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_504_54$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_504_54$epi$surveil.detected)) / ncol(mrsa_sim_504_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_504_54$epi$surveil.cohort/mrsa_sim_504_54$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_504_54$epi$surveil.cohort/mrsa_sim_504_54$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))

#indicators for table: 672 surveillance, 54% hygiene
load("mrsa_sim_672_54.RData")

sum(!is.na(mrsa_sim_672_54$epi$surveil.detected)) / ncol(mrsa_sim_672_54$epi$surveil.detected)

mean(colSums(mrsa_sim_672_54$epi$surveil.active, na.rm=T), na.rm=T) / network_steps
quantile(colSums(mrsa_sim_672_54$epi$surveil.active, na.rm=T) / network_steps, probs=c(0.025,0.975)) 

mean(colSums(mrsa_sim_672_54$epi$surveil.detected, na.rm=T), na.rm=T) / (sum(!is.na(mrsa_sim_672_54$epi$surveil.detected)) / ncol(mrsa_sim_672_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_672_54$epi$surveil.detected, na.rm=T) / (sum(!is.na(mrsa_sim_672_54$epi$surveil.detected)) / ncol(mrsa_sim_672_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_54$epi$surveil.detected, na.rm=T), na.rm=T)
quantile(colSums(mrsa_sim_672_54$epi$surveil.detected, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_672_54$epi$surveil.decolon.success, na.rm=T), na.rm=T)
quantile(colMeans(mrsa_sim_672_54$epi$surveil.decolon.success, na.rm=T), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_672_54$epi$surveil.decolon.success / (mrsa_sim_672_54$epi$surveil.decolon.success+mrsa_sim_672_54$epi$surveil.decolon.fail), na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_672_54$epi$surveil.decolon.success / (mrsa_sim_672_54$epi$surveil.decolon.success+mrsa_sim_672_54$epi$surveil.decolon.fail), na.rm=T) * 100, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_54$epi$surveil.decolon.success.colonizedtime, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_672_54$epi$surveil.detected)) / ncol(mrsa_sim_672_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_672_54$epi$surveil.decolon.success.colonizedtime, na.rm=T) / (sum(!is.na(mrsa_sim_672_54$epi$surveil.detected)) / ncol(mrsa_sim_672_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_54$epi$i.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_672_54$epi$i.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_54$epi$s.num.location.isolation, na.rm=T),na.rm=T) / network_steps
quantile(colSums(mrsa_sim_672_54$epi$s.num.location.isolation, na.rm=T) / network_steps, probs=c(0.025,0.975))

mean(colSums(mrsa_sim_672_54$epi$surveil.cohort, na.rm=T),na.rm=T) / (sum(!is.na(mrsa_sim_672_54$epi$surveil.detected)) / ncol(mrsa_sim_672_54$epi$surveil.detected))
quantile(colSums(mrsa_sim_672_54$epi$surveil.cohort, na.rm=T) / (sum(!is.na(mrsa_sim_672_54$epi$surveil.detected)) / ncol(mrsa_sim_672_54$epi$surveil.detected)), probs=c(0.025,0.975))

mean(colMeans(mrsa_sim_672_54$epi$surveil.cohort/mrsa_sim_672_54$epi$surveil.known.i, na.rm=T),na.rm=T) * 100
quantile(colMeans(mrsa_sim_672_54$epi$surveil.cohort/mrsa_sim_672_54$epi$surveil.known.i, na.rm=T) * 100, probs=c(0.025,0.975))
