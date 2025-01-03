#################################################################################
### This file provides R codes to implement the conditional modeling approach ###
### proposed by Han, Yang, Zhang, Wang, and Liu (2024) in "A conditional 	  ###
### modeling approach for dynamic risk prediction of a survival outcome using ###
### longitudinal biomarkers with an application to ovarian cancer". 		  ###
###																			  ###
### Yongli Justin Han, PhD, Biostatistics Branch, Division of Cancer 		  ###
### Epidemiology and Genetics, National Cancer Institute, National Institutes ###
### of Health																  ###
### Email: yongli.han@nih.gov 												  ###
#################################################################################	

################################################################################
## needed packages
library(mvtnorm)
library(nlme)
library(numDeriv)
library(statmod)
library(survival)
library(JM)
library(survivalROC)

################################################################################
#### kernel function: exponential kernel
G.exp = function(dT, eta2){
  ## exponential kernel without multiplying eta1
  ## dT = Si-tij
  exp(-dT*eta2)
}

################################################################################
#### kernel function: Gaussian kernel
G.gas = function(dT, eta2, eta3) {
  ## dT = Si-tij
  exp(-(dT - eta2)^2/eta3)
}

################################################################################
#### kernel function: latent changepoint kernel
G.lat = function(dT, eta2) {
  ## dT = Si-tij
  ifelse(-dT + eta2 > 0, -dT + eta2, 0)
}


################################################################################
##### loglikelihood function for the piecewise constant proportional hazard model using age as covariate
pwcPHlik <- function(thS, TT, DT, Wmat, lam.knot = lam.knot) {
  ## thS: parameters: piecewise constant baseline hazard and the coefficients
  ## TT:  time in the likelihood
  ## DT: disease status
  ## Wmat: design matrix in the exp function
  ## lam.knot: time threshold for the piecewise constant hazard
  alp = thS[1]
  lam0 = exp(thS[2:3])
  lam0.fun = stepfun(x = c(0, lam.knot), y = c(0, lam0))
  temp = outer(TT, lam.knot, "-")
  temp1 = temp*(temp > 0)
  ##cumulative baseline hazard evaluated at each observed event time
  LAM0.T = lam0[1]*TT + rowSums(t(t(temp1)*diff(lam0)))
  PH = c(exp(Wmat %*% alp))
  lam0.T = lam0.fun(TT)
  SS = exp(-LAM0.T*PH)
  hh = lam0.T*PH
  logL = log(SS)
  logL[DT == 1] = log(hh[DT == 1]*SS[DT == 1])
  - sum(logL)
}

################################################################################
#### loglikelihood function for CM for cases using exponential kernel
## yij = bt0 + bt1*tij + bt2*agei + eta1*g.exp + bi0 + bi1*g.exp + eij

loglik.exp = function(th, YY, TIME, Xmat, Tlong, ID) {
  ## conditional model likelihood for the cases
  ## Tlong is the observed survival time since trial randomization
  bt = th[1:ncol(Xmat)]
  temp = th[-(1:ncol(Xmat))]
  eta = temp[1:2]
  sigb = exp(temp[3:4])
  rhob = (exp(temp[5]) - 1)/(exp(temp[5]) + 1)
  SIG = diag(sigb^2, length(sigb), length(sigb))
  SIG[1,2] = SIG[2,1] = prod(sigb)*rhob
  sige = exp(temp[6])
  n1 = length(table(ID))
  muY = as.vector(Xmat %*% bt + eta[1]*G.exp(Tlong - TIME, eta[2]))
  Zmat = cbind(1, G.exp(Tlong  - TIME, eta[2]))
  logL = rep(NA, n1)
  for (i in 1:n1) {
    Yi = YY[ID == i]
    mui = muY[ID == i]
    Zi = matrix(Zmat[ID == i, ], ncol = ncol(Zmat))
    sigYi = Zi %*% SIG %*% t(Zi) + diag(sige^2, length(Yi), length(Yi))
    logL[i] = dmvnorm(Yi, mui, sigYi, log = TRUE)
  }
  - sum(logL)
}

################################################################################
### joint density for CM with exponential kernel under biomarker dependent censoring assumption
jointYS.exp.dep = function(ss, Yi, tij, Xi.mat, Wi.mat, bt, eta, SIG, sige, 
                           alp, lam0, lam.knot, bt0, X0i.mat, SIG0, sige0, Z0i.mat, KM.C, is.true) {
  ## calculate the joint density of (Yi,Ti=ss)|Xi
  # s: the time since which to evaluate the joint density: time since randomization
  # uu: the time at which to evaluate the joint density: time since randomization, uu > ss
  # Yi: longitudinal vector of biomarkers
  # tij: observation time Yi
  # Xi.mat: design matrix for Yi in the case model, e.g., cbind(1, TIME, AGE)
  # Wi.mat: design matrix for Cox model, e.g., cbind(AGE)
  # bt: fixed effects of Xi.mat in the case model
  # eta: coefficients of exponential kernel
  # SIG: variance matrix of random effects in the case model
  # sige: standard deviation of random error in the case model
  # alp: coefficients of Wi.mat in the Cox model
  # lam0: baseline hazard in the Cox model (piecewise constant)
  # lam.knot: knot of baseline hazard in the Cox model
  # bt0: fixed effects of X0i.mat in the control model
  # X0i.mat: design matrix of Yi in the control model, e.g., cbind(1, TIME, AGE)
  # SIG0: variance matrix of random effects in the control model
  # sige0: standard deviation of random error in the control model
  # Z0i.mat: design matrix of the random effects of Yi in the control model
  # KM.C: KM fit object of the censoring distribution using survfit
  
  ### likelihood for the survival function
  RES = rep(NA, length(ss))
  temp = outer(ss, lam.knot, "-")
  temp1 = temp*(temp > 0)
  LAM0.T = lam0[1]*ss + rowSums(t(t(temp1)*diff(lam0)))
  lam0.fun = stepfun(x = c(0, lam.knot), y = c(0, lam0))
  lam0.T = lam0.fun(ss)
  PH = c(exp(Wi.mat %*% alp))
  fT.log = (-LAM0.T*PH) + log(lam0.T) + log(PH)
  
  ### likelihood for the case model
  fY.log = fT.log*NA
  for (i in 1:length(ss)) {
    ssi = ss[i]
    muY = c(Xi.mat %*% bt + eta[1]*G.exp(ssi - tij, eta[2]))
    Zi.mat = cbind(1, G.exp(ssi - tij, eta[2]))
    sigY = Zi.mat %*% SIG %*% t(Zi.mat) + diag(sige^2, length(Yi), length(Yi))
    fY.log[i] = dmvnorm(Yi, muY, sigY, log = TRUE)
  }
  
  ### likelihood for the control model
  muY0 = c(X0i.mat %*% bt0)
  sigY0 = Z0i.mat %*% SIG0 %*% t(Z0i.mat) + diag(sige0^2, length(Yi), length(Yi))
  fY0.log = dmvnorm(Yi, muY0, sigY0, log = TRUE)
  
  ### the censoring distribution from the Kaplan-Meier estimate
  maxT = max(summary(KM.C)$time)
  minT = min(summary(KM.C)$time)
  temp0 = which(ss < minT)
  temp1 = which((ss >= minT) & (ss <= maxT))
  temp2 = which(ss > maxT)
  surv.C = ss*NA
  surv.C[temp0] = 1
  if (length(temp1) > 0 & is.true == FALSE) {
    surv.C[temp1] = summary(KM.C, times = ss[temp1])$surv
  } else {
    surv.C[temp1] = exp(-1e-3*ss[temp1])
  }
  surv.C[temp2] = 0
  RES = exp(fY.log + fT.log)*surv.C + exp(fY0.log + fT.log)*(1 - surv.C)
  RES
}

################################################################################
#### function to predict risks for CM using exponential kernel
pred.exp.dep <- function(th1, Yi, tij, Xi.mat, Wi.mat, X0i.mat, Z0i.mat, lam.knot, 
                         tstart, pred.gap, KM.C, is.true) {
  # predict the kth year disease probability since the given observation time tstart
  # tstart = s: start time for the prediction 
  # pred.gap = tau: time gap between the prediction time and the start time
  # Xi.mat: design matrix for fixed effects of the case model
  # Wi.mat: design matrix for the survival model
  # X0i.mat: design matrix for fixed effects of the control model
  # Z0i.mat: design matrix for random effects of the control model
  # lam.knot: threshold for the piecewise constant hazard
  # tstart: time since when to make risk prediction
  # year: the year of interest for risk prediction given the observation time s
  # KM.C: the estimated censoring distribution
  
  # set all parameters into a vector for later derivative calculation
  bt = th1[1:ncol(Xi.mat)]
  temp = th1[-(1:ncol(Xi.mat))]
  eta = temp[1:2]
  sigb = exp(temp[3:4])
  rhob = (exp(temp[5]) - 1)/(exp(temp[5]) + 1)
  SIG = diag(sigb^2, length(sigb), length(sigb))
  SIG[1, 2] = SIG[2, 1] = prod(sigb)*rhob
  sige = exp(temp[6])
  
  bt0 = temp[7:9]
  temp0 = temp[10:12]
  SIG0 = diag(c(temp0[1]^2, temp0[2]^2), 2, 2)
  SIG0[2, 1] = SIG0[1, 2] = prod(temp0)
  sige0 = temp[13]
  
  alp = temp[14]
  lam0 = exp(temp[15:16])
  
  ###### Note: integrate is better than gauss_kronrod due to integrated value and rel.error
  DEN = integrate(jointYS.exp.dep,
                  lower = tstart, upper = Inf,
                  Yi = Yi, tij = tij, 
                  Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta, SIG = SIG, sige = sige,
                  alp = alp, lam0 = lam0, lam.knot = lam.knot,
                  bt0 = bt0, X0i.mat = X0i.mat, SIG0 = SIG0, sige0 = sige0, Z0i.mat = Z0i.mat,
                  KM.C = KM.C, is.true, subdivisions = 1e5)
  NUM = integrate(jointYS.exp.dep,
                  lower = tstart, upper = tstart + pred.gap,
                  Yi = Yi, tij = tij, 
                  Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta, SIG = SIG, sige = sige,
                  alp = alp, lam0 = lam0, lam.knot = lam.knot,
                  bt0 = bt0, X0i.mat = X0i.mat, SIG0 = SIG0, sige0 = sige0, Z0i.mat = Z0i.mat,
                  KM.C = KM.C, is.true, subdivisions = 1e5)
  temp = NUM$value/DEN$value
  temp = ifelse(temp > 1, 1, temp)
  temp = ifelse(temp < 0, 0, temp)
  P.logit = qlogis(temp)
  P.logit
}

################################################################################
### joint density for cm with exponential kernel under biomarker independent censoring assumption
jointYS.exp.ind = function(ss, Yi, tij, Xi.mat, Wi.mat, bt, eta, SIG, sige, alp, lam0, lam.knot) {
  ## calculate the joint density of (Yi,Ti=ss)|Xi
  #ss: survival time to evaluate the joint density: time since last biomarker observation
  #Yi: longitudinal vector of biomarkers
  #tij: observation time Yi
  #Xi.mat: design matrix for Yi in the case model, e.g., cbind(1,TIME,AGE)
  #Wi.mat: design matrix for Cox model, e.g., cbind(AGE)
  #bt: fixed effects of Xi.mat in the case model
  #eta: coefficients of exponential kernel
  #SIG: variance matrix of random effects in the case model
  #sige: standard deviation of random error in the case model
  #alp: coefficients of Wi.mat in the Cox model
  #lam0: baseline hazard in the Cox model (piecewise constant)
  #lam.knot: knot of baseline hazard in the Cox model
  RES = rep(NA,length(ss))
  temp = outer(ss,lam.knot,"-")
  temp1 = temp*(temp>0)
  LAM0.T = lam0[1]*ss + rowSums(t(t(temp1)*diff(lam0)))
  lam0.fun = stepfun(x=c(0,lam.knot),y=c(0,lam0))
  lam0.T=lam0.fun(ss)
  PH=c(exp(Wi.mat%*%alp))
  fT.log=(-LAM0.T*PH)+log(lam0.T)+log(PH)
  fY.log=fT.log*NA
  for(i in 1:length(ss)){
    ssi=ss[i]
    muY= c(Xi.mat %*% bt + eta[1]*G.exp(ssi - tij,eta[2]))
    Zi.mat = cbind(1,G.exp(ssi - tij,eta[2]))
    sigY = Zi.mat %*% SIG %*% t(Zi.mat) + diag(sige^2, length(Yi), length(Yi))
    fY.log[i] = dmvnorm(Yi, muY, sigY, log = TRUE)
  }
  RES=exp(fY.log+fT.log)
  RES
}

################################################################################
pred.exp.ind = function(th1, Yi, tij, Xi.mat, Wi.mat, lam.knot, tstart, pred.gap){
  ## predict k year disease probability after the last observation
  bt = th1[1:ncol(Xi.mat)]
  temp = th1[-(1:ncol(Xi.mat))]
  eta = temp[1:2]
  sigb = exp(temp[3:4])
  rhob = (exp(temp[5])-1)/(exp(temp[5])+1)
  SIG = diag(sigb^2)
  SIG[1, 2] = SIG[2, 1]=prod(sigb)*rhob
  sige = exp(temp[6])
  
  alp = temp[7]
  lam0 = exp(temp[8:9])
  
  DEN = integrate(jointYS.exp.ind,
                  lower = tstart,upper = Inf,
                  Yi = Yi, tij = tij, Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta,
                  SIG = SIG, sige = sige, alp = alp, lam0 = lam0, lam.knot = lam.knot)
  NUM = integrate(jointYS.exp.ind,
                  lower = tstart, upper= tstart + pred.gap,
                  Yi = Yi, tij = tij, Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta,
                  SIG = SIG, sige = sige, alp = alp, lam0 = lam0, lam.knot = lam.knot)
  temp = NUM$value/DEN$value
  temp = ifelse(temp > 1, 1, temp)
  temp = ifelse(temp < 0, 0, temp)
  P.logit = qlogis(temp)
  return(P.logit)
}

################################################################################
## loglikelihood of CM using Gaussian kernel
loglik.gas = function(th, YY, TIME, Xmat, Tlong, ID) {
  ## conditional model likelihood for the cases
  ## Tlong is the observed survival time since trial randomization
  bt = th[1:ncol(Xmat)]
  temp = th[-(1:ncol(Xmat))]
  eta = temp[1:3]
  sigb = exp(temp[4:5])
  rhob = (exp(temp[6]) - 1)/(exp(temp[6]) + 1)
  SIG = diag(sigb^2, length(sigb), length(sigb))
  SIG[1, 2] = SIG[2, 1] = prod(sigb)*rhob
  sige = exp(temp[7])
  n1 = length(table(ID))
  muY = c(Xmat %*% bt + eta[1]*G.gas(Tlong - TIME, eta[2], eta[3]))
  Zmat = cbind(1, G.gas(Tlong  - TIME, eta[2], eta[3]))
  logL = rep(NA, n1)
  for (i in 1:n1) {
    Yi = YY[ID == i]
    mui = muY[ID == i]
    Zi = matrix(Zmat[ID == i, ], ncol = ncol(Zmat))
    sigYi = Zi %*% SIG %*% t(Zi) + diag(sige^2, length(Yi), length(Yi))
    logL[i] = dmvnorm(Yi, mui, sigYi, log = TRUE)
  }
  - sum(logL)
}

################################################################################

jointYS.gas.dep = function(ss, Yi, tij, Xi.mat, Wi.mat, bt, eta, SIG, sige, 
                           alp, lam0, lam.knot, bt0, X0i.mat, SIG0, sige0, Z0i.mat, KM.C, is.true) {
  ## calculate the joint density of (Yi,Ti=ss)|Xi
  #ss: survival time to evaluate the joint density: time since last biomarker observation
  #Yi: longitudinal vector of biomarkers
  #tij: observation time Yi
  #Xi.mat: design matrix for Yi in the case model, e.g., cbind(1,TIME,AGE)
  #Wi.mat: design matrix for Cox model, e.g., cbind(AGE)
  #bt: fixed effects of Xi.mat in the case model
  #eta: coefficients of exponential kernel
  #SIG: variance matrix of random effects in the case model
  #sige: standard deviation of random error in the case model
  #alp: coefficients of Wi.mat in the Cox model
  #lam0: baseline hazard in the Cox model (piecewise constant)
  #lam.knot: knot of baseline hazard in the Cox model
  #bt0: fixed effects of X0i.mat in the control model
  #X0i.mat: design matrix of Yi in the control model, e.g., cbind(1,TIME,AGE)
  #SIG0: variance matrix of random effects in the control model
  #sige0: standard deviation of random error in the control model
  #Z0i.mat: design matrix of the random effects of Yi in the control model
  #fitC: KM fit object of the censoring distribution using survfit
  
  ### likelihood for the survival function
  RES = rep(NA,length(ss))
  temp = outer(ss, lam.knot, "-")
  temp1 = temp*(temp > 0)
  LAM0.T = lam0[1]*ss + rowSums(t(t(temp1)*diff(lam0)))
  lam0.fun = stepfun(x = c(0,lam.knot), y = c(0, lam0))
  lam0.T = lam0.fun(ss)
  PH = c(exp(Wi.mat%*%alp))
  fT.log = (-LAM0.T*PH) + log(lam0.T) + log(PH)
  
  ### likelihood for the case model
  fY.log = fT.log*NA
  for(i in 1:length(ss)){
    ssi = ss[i]
    muY = c(Xi.mat %*% bt + eta[1]*G.gas(ssi - tij, eta[2], eta[3]))
    Zi.mat = cbind(1, G.gas(ssi - tij, eta[2], eta[3]))
    sigY = Zi.mat %*% SIG %*% t(Zi.mat) + diag(sige^2, length(Yi))
    fY.log[i] = dmvnorm(Yi, muY, sigY, log = TRUE)
  }
  
  ### likelihood for the control model
  muY0 = c(X0i.mat %*% bt0)
  sigY0 = Z0i.mat %*% SIG0 %*% t(Z0i.mat) + diag(sige0^2, length(Yi))
  fY0.log = dmvnorm(Yi, muY0, sigY0, log = TRUE)
  
  
  maxT = max(summary(KM.C)$time)
  minT = min(summary(KM.C)$time)
  temp0 = which(ss<minT)
  temp1 = which((ss>=minT)&(ss<=maxT))
  temp2 = which(ss>maxT)
  surv.C = ss*NA
  surv.C[temp0] = 1
  surv.C[temp2] = 0
  if (length(temp1) > 0 & is.true == FALSE) {
    surv.C[temp1] = summary(KM.C, times = ss[temp1])$surv
  } else {
    surv.C[temp1] = exp(-1e-3*ss[temp1])
  }
  RES = exp(fY.log + fT.log)*surv.C + exp(fY0.log + fT.log)*(1 - surv.C)
  RES
}

################################################################################
pred.gas.dep = function(th1, Yi, tij, Xi.mat, Wi.mat, X0i.mat, Z0i.mat, lam.knot, 
                        tstart, pred.gap, KM.C, is.true) {
  ## predict k year disease probability after the last observation
  bt = th1[1:ncol(Xi.mat)]
  temp = th1[-(1:ncol(Xi.mat))]
  eta = temp[1:3]
  sigb = exp(temp[4:5])
  rhob = (exp(temp[6]) - 1)/(exp(temp[6]) + 1)
  SIG = diag(sigb^2, length(sigb), length(sigb))
  SIG[1, 2] = SIG[2, 1] = prod(sigb)*rhob
  sige = exp(temp[7])
  
  bt0 = temp[8:10]
  temp0 = temp[11:13]
  SIG0 = diag(c(temp0[1]^2, temp0[2]^2), 2, 2)
  SIG0[2, 1] = SIG0[1, 2] = prod(temp0)
  sige0 = temp[14]
  
  alp = temp[15]
  lam0 = exp(temp[16:17])
  
  DEN = integrate(jointYS.gas.dep,
                  lower = tstart, upper = Inf,
                  Yi = Yi, tij = tij, 
                  Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta, SIG = SIG, sige = sige,
                  alp = alp, lam0 = lam0, lam.knot = lam.knot,
                  bt0 = bt0, X0i.mat = X0i.mat, SIG0 = SIG0, sige0 = sige0, Z0i.mat = Z0i.mat,
                  KM.C = KM.C, is.true = is.true, subdivisions = 1e4)
  NUM = integrate(jointYS.gas.dep,
                  lower = tstart, upper = tstart + pred.gap,
                  Yi = Yi, tij = tij, 
                  Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta, SIG = SIG, sige = sige,
                  alp = alp, lam0 = lam0, lam.knot = lam.knot,
                  bt0 = bt0, X0i.mat = X0i.mat, SIG0 = SIG0, sige0 = sige0, Z0i.mat = Z0i.mat,
                  KM.C = KM.C, is.true = is.true, subdivisions = 1e4)
  temp = NUM$value/DEN$value
  temp = ifelse(temp > 1, 1, temp)
  temp = ifelse(temp < 0, 0, temp)
  P.logit = qlogis(temp)
  P.logit
}

################################################################################
jointYS.gas.ind = function(ss, Yi, tij, Xi.mat, Wi.mat, bt, eta, SIG, sige, alp, lam0, lam.knot) {
  RES = rep(NA,length(ss))
  temp = outer(ss,lam.knot,"-")
  temp1 = temp*(temp>0)
  LAM0.T = lam0[1]*ss+rowSums(t(t(temp1)*diff(lam0)))
  lam0.fun = stepfun(x=c(0,lam.knot),y=c(0,lam0))
  lam0.T = lam0.fun(ss)
  PH = c(exp(Wi.mat%*%alp))
  fT.log = (-LAM0.T*PH)+log(lam0.T)+log(PH)
  fY.log = fT.log*NA
  for(i in 1:length(ss)){
    ssi = ss[i]
    muY = c(Xi.mat %*% bt + eta[1]*G.gas(ssi - tij, eta[2], eta[3]))
    Zi.mat = cbind(1, G.gas(ssi - tij, eta[2], eta[3]))
    sigY = Zi.mat %*% SIG %*% t(Zi.mat) + diag(sige^2, length(Yi), length(Yi))
    fY.log[i] = dmvnorm(Yi, muY, sigY, log = TRUE)
  }
  RES = exp(fY.log+fT.log)
  RES
}

################################################################################
pred.gas.ind = function(th1, Yi, tij, Xi.mat, Wi.mat, lam.knot, tstart, pred.gap) {
  ## predict k year disease probability after the last observation
  bt = th1[1:ncol(Xi.mat)]
  temp = th1[-(1:ncol(Xi.mat))]
  eta = temp[1:3]
  sigb = exp(temp[4:5])
  rhob = (exp(temp[6])-1)/(exp(temp[6])+1)
  SIG = diag(sigb^2)
  SIG[1, 2] = SIG[2, 1]=prod(sigb)*rhob
  sige = exp(temp[7])
  
  alp = temp[8]
  lam0 = exp(temp[9:10])
  
  DEN = integrate(jointYS.gas.ind,
                  lower = tstart, upper = Inf,
                  Yi = Yi, tij = tij, Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta,
                  SIG = SIG, sige = sige, alp = alp, lam0 = lam0, lam.knot = lam.knot)
  NUM = integrate(jointYS.gas.ind,
                  lower = tstart, upper= tstart + pred.gap,
                  Yi = Yi, tij = tij, Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta,
                  SIG = SIG, sige = sige, alp = alp, lam0 = lam0, lam.knot = lam.knot)
  temp = NUM$value/DEN$value
  temp = ifelse(temp > 1, 1, temp)
  temp = ifelse(temp < 0, 0, temp)
  P.logit = qlogis(temp)
  return(P.logit)
}

################################################################################
#### with fixed changepoint eta[2]
loglik.lat = function(th, YY, TIME, Xmat, Tlong, ID) {
  
  bt = th[1:ncol(Xmat)]
  temp = th[-(1:ncol(Xmat))]
  eta = temp[1:2]
  sigb = exp(temp[3:4])
  rhob = (exp(temp[5]) - 1)/(exp(temp[5]) + 1)
  SIG = diag(sigb^2, length(sigb), length(sigb))
  SIG[1,2] = SIG[2,1] = prod(sigb)*rhob
  sige = exp(temp[6])
  n1 = length(table(ID))
  muY = c(Xmat %*% bt + eta[1]*G.lat(Tlong - TIME, eta[2]))
  Zmat = cbind(1, G.lat(Tlong  - TIME, eta[2]))
  logL = rep(NA, n1)
  for (i in 1:n1) {
    Yi = YY[ID == i]
    mui = muY[ID == i]
    Zi = matrix(Zmat[ID == i, ], ncol = ncol(Zmat))
    sigYi = Zi %*% SIG %*% t(Zi) + diag(sige^2, length(Yi), length(Yi))
    logL[i] = dmvnorm(Yi, mui, sigYi, log = TRUE)
  }
  - sum(logL)
}

################################################################################
jointYS.lat.dep = function(ss, Yi, tij, Xi.mat, Wi.mat, bt, eta, SIG, sige, 
                           alp, lam0, lam.knot, bt0, X0i.mat, SIG0, sige0, Z0i.mat, KM.C, is.true) {
  ## calculate the joint density of (Yi,Ti=ss)|Xi
  #ss: survival time to evaluate the joint density: time since last biomarker observation
  #Yi: longitudinal vector of biomarkers
  #tij: observation time Yi
  #Xi.mat: design matrix for Yi in the case model, e.g., cbind(1,TIME,AGE)
  #Zi.mat: design matrix for Cox model, e.g., cbind(1, TIME)
  #bt: fixed effects of Xi.mat in the case model
  #eta: coefficients of exponential kernel
  #SIG: variance matrix of random effects in the case model
  #sige: standard deviation of random error in the case model
  #alp: coefficients of Wi.mat in the Cox model
  #lam0: baseline hazard in the Cox model (piecewise constant)
  #lam.knot: knot of baseline hazard in the Cox model
  #bt0: fixed effects of X0i.mat in the control model
  #X0i.mat: design matrix of Yi in the control model, e.g., cbind(1,TIME,AGE)
  #SIG0: variance matrix of random effects in the control model
  #sige0: standard deviation of random error in the control model
  #Z0i.mat: design matrix of the random effects of Yi in the control model
  #fitC: KM fit object of the censoring distribution using survfit
  
  ### likelihood for the survival function
  RES = rep(NA, length(ss))
  temp = outer(ss, lam.knot, "-")
  temp1 = temp*(temp > 0)
  LAM0.T = lam0[1]*ss + rowSums(t(t(temp1)*diff(lam0)))
  lam0.fun = stepfun(x = c(0, lam.knot), y = c(0, lam0))
  lam0.T = lam0.fun(ss)
  PH = c(exp(Wi.mat %*% alp))
  fT.log = (-LAM0.T*PH) + log(lam0.T) + log(PH)
  
  ### likelihood for the case model
  fY.log = fT.log*NA
  for (i in 1:length(ss)) {
    ssi = ss[i]
    muY = c(Xi.mat %*% bt + eta[1]*G.lat(ssi - tij, eta[2]))
    Zi.mat = cbind(1, G.lat(ssi - tij, eta[2]))
    sigY = Zi.mat %*% SIG %*% t(Zi.mat) + diag(sige^2, length(Yi), length(Yi))
    fY.log[i] = dmvnorm(Yi, muY, sigY, log = TRUE)
  }
  
  ### likelihood for the control model
  muY0 = c(X0i.mat %*% bt0)
  sigY0 = Z0i.mat %*% SIG0 %*% t(Z0i.mat) + diag(sige0^2, length(Yi), length(Yi))
  fY0.log = dmvnorm(Yi, muY0, sigY0, log = TRUE)
  
  ### the censoring distribution from the Kaplan-Meier estimate
  maxT = max(summary(KM.C)$time)
  minT = min(summary(KM.C)$time)
  temp0 = which(ss < minT)
  temp1 = which((ss >= minT) & (ss <= maxT))
  temp2 = which(ss > maxT)
  surv.C = ss*NA
  surv.C[temp0] = 1
  surv.C[temp2] = 0
  if (length(temp1) > 0 & is.true == FALSE) {
    surv.C[temp1] = summary(KM.C, times = ss[temp1])$surv
  } else {
    surv.C[temp1] = exp(-1e-3*ss[temp1])
  }
  RES = exp(fY.log + fT.log)*surv.C + exp(fY0.log + fT.log)*(1 - surv.C)
  RES
}
################################################################################

pred.lat.dep = function(th1, Yi, tij, Xi.mat, Wi.mat, X0i.mat, Z0i.mat, lam.knot, tstart, pred.gap, KM.C, is.true) {
  ## predict k year disease probability after the last observation
  # set all parameters into a vector for later derivative calculation
  bt = th1[1:ncol(Xi.mat)]
  temp = th1[-(1:ncol(Xi.mat))]
  eta = temp[1:2]
  sigb = exp(temp[3:4])
  rhob = (exp(temp[5]) - 1)/(exp(temp[5]) + 1)
  SIG = diag(sigb^2, length(sigb), length(sigb))
  SIG[1, 2] = SIG[2, 1] = prod(sigb)*rhob
  sige = exp(temp[6])
  
  bt0 = temp[7:9]
  temp0 = temp[10:12]
  SIG0 = diag(c(temp0[1]^2, temp0[2]^2), 2, 2)
  SIG0[2, 1] = SIG0[1, 2] = prod(temp0)
  sige0 = temp[13]
  
  alp = temp[14]
  lam0 = exp(temp[15:16])
  
  DEN = integrate(jointYS.lat.dep,
                  lower = tstart, upper = Inf,
                  Yi = Yi, tij = tij, 
                  Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta, SIG = SIG, sige = sige,
                  alp = alp, lam0 = lam0, lam.knot = lam.knot,
                  bt0 = bt0, X0i.mat = X0i.mat, SIG0 = SIG0, sige0 = sige0, Z0i.mat = Z0i.mat,
                  KM.C = KM.C, is.true = is.true, subdivisions = 1e4)
  NUM = integrate(jointYS.lat.dep,
                  lower = tstart, upper = tstart + pred.gap,
                  Yi = Yi, tij = tij, 
                  Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta, SIG = SIG, sige = sige,
                  alp = alp, lam0 = lam0, lam.knot = lam.knot,
                  bt0 = bt0, X0i.mat = X0i.mat, SIG0 = SIG0, sige0 = sige0, Z0i.mat = Z0i.mat,
                  KM.C = KM.C, is.true = is.true, subdivisions = 1e4)
  temp = NUM$value/DEN$value
  temp = ifelse(temp > 1, 1, temp)
  temp = ifelse(temp < 0, 0, temp)
  P.logit = qlogis(temp)
  P.logit
}

################################################################################
jointYS.lat.ind = function(ss, Yi, tij, Xi.mat, Wi.mat, bt, eta, SIG, sige, alp,lam0, lam.knot) {
  ## calculate the joint density of (Yi,Ti=ss)|Xi
  #ss: survival time to evaluate the joint density: time since last biomarker observation
  #Yi: longitudinal vector of biomarkers
  #tij: observation time Yi
  #Xi.mat: design matrix for Yi in the case model, e.g., cbind(1,TIME,AGE)
  #Zi.mat: design matrix for Cox model, e.g., cbind(1, TIME)
  #bt: fixed effects of Xi.mat in the case model
  #eta: coefficients of exponential kernel
  #SIG: variance matrix of random effects in the case model
  #sige: standard deviation of random error in the case model
  #alp: coefficients of Wi.mat in the Cox model
  #lam0: baseline hazard in the Cox model (piecewise constant)
  #lam.knot: knot of baseline hazard in the Cox model
  RES = rep(NA, length(ss))
  temp = outer(ss, lam.knot, "-")
  temp1 = temp*(temp > 0)
  LAM0.T = lam0[1]*ss + rowSums(t(t(temp1)*diff(lam0)))
  lam0.fun = stepfun(x = c(0, lam.knot), y = c(0, lam0))
  lam0.T = lam0.fun(ss)
  PH = c(exp(Wi.mat %*% alp))
  fT.log = (-LAM0.T*PH) + log(lam0.T) + log(PH)
  
  ### likelihood for the case model
  fY.log = fT.log*NA
  for (i in 1:length(ss)) {
    ssi = ss[i]
    muY = c(Xi.mat %*% bt + eta[1]*G.lat(ssi - tij, eta[2]))
    Zi.mat = cbind(1, G.lat(ssi - tij, eta[2]))
    sigY = Zi.mat %*% SIG %*% t(Zi.mat) + diag(sige^2, length(Yi), length(Yi))
    fY.log[i] = dmvnorm(Yi, muY, sigY, log = TRUE)
  }
  
  RES = exp(fY.log + fT.log)
  RES
}

################################################################################
pred.lat.ind = function(th1, Yi, tij, Xi.mat, Wi.mat, lam.knot, tstart, pred.gap) {
  ## predict k year disease probability after the last observation
  bt = th1[1:ncol(Xi.mat)]
  temp = th1[-(1:ncol(Xi.mat))]
  eta = temp[1:2]
  sigb = exp(temp[3:4])
  rhob = (exp(temp[5])-1)/(exp(temp[5])+1)
  SIG = diag(sigb^2)
  SIG[1, 2] = SIG[2, 1]=prod(sigb)*rhob
  sige = exp(temp[6])
  
  alp = temp[7]
  lam0 = exp(temp[8:9])
  
  DEN = integrate(jointYS.lat.ind,
                  lower = tstart,upper = Inf,
                  Yi = Yi, tij = tij, Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta,
                  SIG = SIG, sige = sige, alp = alp, lam0 = lam0, lam.knot = lam.knot)
  NUM = integrate(jointYS.lat.ind,
                  lower = tstart, upper= tstart + pred.gap,
                  Yi = Yi, tij = tij, Xi.mat = Xi.mat, Wi.mat = Wi.mat, bt = bt, eta = eta,
                  SIG = SIG, sige = sige, alp = alp, lam0 = lam0, lam.knot = lam.knot)
  temp = NUM$value/DEN$value
  temp = ifelse(temp > 1, 1, temp)
  temp = ifelse(temp < 0, 0, temp)
  P.logit = qlogis(temp)
  return(P.logit)
}


################################################################################
### covariance matrix for fitted parameters
var.fitted.para.func <- function(fit.exp, fit.con, fitS, censor.type) {
  # fitted case model: fit.exp
  # fitted control model: fit.con
  # fitted survival function: fitS
  th.cs = as.vector(fit.exp$par)
  th.surv = as.vector(fitS$par)
  
  if (censor.type == 'dependent') {
    th.cn.fixed = as.vector(fit.con$coefficients$fixed)
    temp.rand.mat = getVarCov(fit.con, 'random.effects')
    th.cn.random = c(as.vector(sqrt(diag(temp.rand.mat))), cov2cor(temp.rand.mat)[2, 1], fit.con$sigma)
    th = c(th.cs, th.cn.fixed, th.cn.random, th.surv)
    vmat =  matrix(0, length(th), length(th))
    loc1 = 1:length(th.cs);
    loc2 = (length(th.cs) + 1):(length(th.cs) + length(th.cn.fixed))
    loc3 = (length(th.cs) + length(th.cn.fixed) + 1):(length(th.cs) + length(th.cn.fixed) + length(th.cn.random))
    loc4 = (length(th.cs) + length(th.cn.fixed) + length(th.cn.random) + 1):length(th)
    vmat[loc1, loc1] = solve(fit.exp$hessian)
    vmat[loc2, loc2] = fit.con$varFix
    vmat[loc3, loc3] = fit.con$apVar
    vmat[loc4, loc4] = solve(fitS$hessian)
  } else {
    th = c(th.cs, th.surv)
    vmat =  matrix(0, length(th), length(th))
    loc1 = 1:length(th.cs)
    loc2 = (length(th.cs) + 1):length(th)
    vmat[loc1, loc1] = solve(fit.exp$hessian)
    vmat[loc2, loc2] = solve(fitS$hessian)
  }
  return(vmat)
}

################################################################################
### partial derivative matrix of predicted risks with regard to fitted parameters
mat.parderiv.para.func <- function(pred.exp.dep, Pmat.exp.dep, fit.exp, fit.con, fitS, Yi, tij, Xi.mat, 
                                   Wi.mat, X0i.mat, Z0i.mat, lam.knot, ss, tau, KM.C, censor.type) {
  # Pmat.exp.dep: predicted risks
  # fitted case model: fit.exp
  # fitted control model: fit.con
  # fitted survival function: fitS
  if (censor.type == 'dependent') {
    th.exp.cs = as.vector(fit.exp$par)
    th.cn.fixed0 = as.vector(fit.con$coefficients$fixed)
    temp.rand.mat = getVarCov(fit.con, 'random.effects')
    th.cn.random = c(as.vector(sqrt(diag(temp.rand.mat))), cov2cor(temp.rand.mat)[2, 1], fit.con$sigma)
    th.surv = as.vector(fitS$par)
    th1 = c(th.exp.cs, th.cn.fixed0, th.cn.random, th.surv)
    
    deriv.vec = jacobian(func = pred.exp.dep, x = th1, Yi = Yi, tij = tij, Xi.mat = Xi.mat, 
                         Wi.mat = Wi.mat, X0i.mat = X0i.mat,
                         Z0i.mat = Z0i.mat, lam.knot = lam.knot, tstart = ss, pred.gap = tau, KM.C = KM.C, 
                         is.true = F)
  } else {
    th.exp.cs = as.vector(fit.exp$par)
    th.surv = as.vector(fitS$par)
    th1 = c(th.exp.cs, th.surv)
    
    deriv.vec = jacobian(func = pred.exp.dep, x = th1, Yi = Yi, tij = tij, Xi.mat = Xi.mat, 
                         Wi.mat = Wi.mat, lam.knot = lam.knot, tstart = ss, pred.gap = tau)
  }
  
  if ((Pmat.exp.dep == 1) | (Pmat.exp.dep == 0)) {
    deriv.vec = matrix(0, 1, length(deriv.vec))
  }
  return(deriv.vec)
}

################################################################################
##### calculate the standard deviation of the predicted risks
pred.risk.sd.func <- function(pred.exp.dep, Pmat.exp.dep, fit.exp, fit.con, fitS, Yi, tij, Xi.mat, Wi.mat, 
                              X0i.mat, Z0i.mat, lam.knot, ss, tau, KM.C, censor.type) {
  dmat = mat.parderiv.para.func(pred.exp.dep, Pmat.exp.dep, fit.exp, fit.con, fitS, Yi, tij, Xi.mat, Wi.mat, 
                                X0i.mat, Z0i.mat, lam.knot, ss, tau, KM.C, censor.type)
  vmat = var.fitted.para.func(fit.exp, fit.con, fitS, censor.type)
  sqrt(dmat %*% vmat %*% t(dmat))
}

################################################################################
### the 95% confidence interval for the predicted risk
ci95.pred.risk <- function(pred.exp.dep, Pmat.exp.dep, fit.exp, fit.con, fitS, Yi, tij, Xi.mat, Wi.mat, 
                           X0i.mat, Z0i.mat, lam.knot, ss, tau, KM.C, censor.type) {
  sd.pred.risk = pred.risk.sd.func(pred.exp.dep, Pmat.exp.dep, fit.exp, fit.con, fitS, Yi, tij, Xi.mat, 
                                   Wi.mat, X0i.mat, Z0i.mat, lam.knot, ss, tau, KM.C, censor.type)
  ci.lower = plogis(qlogis(Pmat.exp.dep) - 1.96*sd.pred.risk)
  ci.upper = plogis(qlogis(Pmat.exp.dep) + 1.96*sd.pred.risk)
  c(ci.lower, Pmat.exp.dep, ci.upper)
}

################################################################################
### function to trim data for the implementation of the landmark approach
cutdata_func <- function(testing.dat, srt.time, wd.length) {
  ### function to trim dataset according to landmark time srt.time and prediction time wd.length
  # For a given landmark time point srt.time, patients who have reached the event of interest (outcome) or
  # are censored before or at LM are removed.
  # Administrative censoring is applied at the time horizon
  
  testing.dat.used = NULL
  for (ids in unique(testing.dat$ID)) {
    temp.test = testing.dat[testing.dat$ID == ids, ]
    ### remove subjects who did not survival after the landmark time srt.time
    if (max(temp.test$Censor_year) >= srt.time) {
      temp.test = temp.test[temp.test$Screen_year <= srt.time, ] ## only keep observations observed before srt.time
      temp.test = temp.test[nrow(temp.test), ] ## keep the most recent observation for subject ids
    } else {
      temp.test = NULL
    }
    testing.dat.used = rbind(testing.dat.used, temp.test)
  }
  ### Administrative censoring is applied at the time horizon
  testing.dat.used$TT_new = ifelse(testing.dat.used$Censor_year <= srt.time + wd.length, 
                                   testing.dat.used$Censor_year, srt.time + wd.length)
  ### Administrative status modification is applied at the time horizon
  testing.dat.used$DD_new = ifelse(testing.dat.used$Censor_year <= srt.time + wd.length, 
                                   testing.dat.used$DD_status, 0)
  return(testing.dat.used)
}

################################################################################
### simulate data from the conditional modeling approach under the biomarker dependent censoring assumption
cm_dep_simu_data_func <- function(seed, kernel, N) {
  ## kernel: kernel function for the conditional modeling
  ## N: sample size
  set.seed(seed)
  
  ###~~~~~~~~~~~~~~~~~~~~~~~~~~~ control model
  alpc = c(2.03, 0.005, 0.008)
  SIGbc = matrix(c(0.21, -0.002, -0.002, 0.001), 2, 2)
  sigec = 0.2
  
  ###~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  ### age of case and control subjects
  # age.cs = rnorm(N.cs, mean = 63.5, sd = 5.6)
  # age.cn = rnorm(N.cn, mean = 62.3, sd = 5.4)
  age.probs = c(6.598482e-05, 3.299241e-05, 9.897724e-05, 9.722864e-02, 7.472781e-02, 6.426922e-02,
                5.730782e-02, 5.341471e-02, 7.423293e-02, 6.324645e-02, 6.172880e-02, 5.588915e-02,
                5.202903e-02, 4.942263e-02, 4.678324e-02, 4.378093e-02, 3.919499e-02, 3.681953e-02,
                3.467502e-02, 3.055097e-02, 2.652590e-02, 2.273177e-02, 1.517651e-02, 3.299241e-05,
                0, 0, 3.299241e-05)
  Age = sample(52:78, N, replace = T, prob = age.probs)
  
  ###~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
  #### survival time from a piecewise baseline hazard with baseline age as covariate
  t.knot = 2
  uu = runif(N, 0, 1)
  st = -log(uu)/exp(0.04*Age)/exp(-5.63114665)
  st[st > t.knot] = ((-log(uu)/exp(0.04*Age) - exp(-5.63114665)*t.knot)/exp(-5.85505853)+t.knot)[st > t.knot]
  
  ###~~~~~~~~~~~~~~~~~~~~~~~~~~~ censoring time
  # ct = pmin(rexp(N, rate = 0.08854268), 13)
  ct = pmin(rexp(N, rate = 1e-3), 13 + rnorm(N, 0, 0.1))
  
  ###~~~~~~~~~~~~~~~~~~~~~~~~~~~ observed survival time
  tts = pmin(st, ct)
  dd = ifelse(st < ct, 1, 0)
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('Generated cases and controls')
  print(table(dd))
  ni.temp = pmin(tts, 5)
  ni = unlist(sapply(ni.temp, function(x) length(0:x))) # cluster size
  
  ### data generated (long format)
  ID = rep(1:N, ni)
  age.long = rep(Age, ni) ## baseline age long format
  screen_time = unlist(sapply(ni.temp, function(x) {0:x})) # screening time (long format)
  DD = rep(dd, ni)
  TTs = rep(tts, ni)
  
  ### log_ca125 for control subjects
  bb.temp0 = rmvnorm(N, rep(0, 2), sigma = SIGbc); bb.long0 = bb.temp0[ID, ]
  ee.long0 = rnorm(length(ID), 0, sigec)
  log_ca125 = cbind(1, age.long, screen_time) %*% alpc + rowSums(cbind(1, screen_time) * bb.long0) + ee.long0
  
  ### log_ca125 for case subjects
  if (kernel == 'exp') {
    betas = c(2.3, 0.0008, 0.007)
    etas = c(2.84, 1.97)
    sigb0 = exp(-0.73); sigb1 = exp(0.73); rhob = (exp(-0.58)-1)/(exp(-0.58)+1)
    SIGb = matrix(c(sigb0^2, sigb0*sigb1*rhob, sigb0*sigb1*rhob, sigb1^2), 2, 2)
    sige = exp(-1.44)
    
    bb.temp1 = rmvnorm(N, rep(0, 2), sigma = SIGb); bb.long1 = bb.temp1[ID, ]
    ee.long1 = rnorm(length(ID), 0, sige)
    log_ca125.cs = cbind(1, age.long, screen_time) %*% betas + etas[1]*G.exp(TTs - screen_time, etas[2]) + 
      rowSums(cbind(1, G.exp(TTs - screen_time, eta2 = etas[2])) * bb.long1) + ee.long1
  } else if (kernel == 'gas') {
    betas = c(2.3, 0.0008, 0.009)
    etas = c(6.8, -1.4, 2)
    sigb0 = exp(-0.74); sigb1 = exp(1.62); rhob = (exp(-0.58)-1)/(exp(-0.58)+1)
    SIGb = matrix(c(sigb0^2, sigb0*sigb1*rhob, sigb0*sigb1*rhob, sigb1^2), 2, 2)
    sige = exp(-1.44)
    
    bb.temp1 = rmvnorm(N, rep(0, 2), sigma = SIGb); bb.long1 = bb.temp1[ID, ]
    ee.long1 = rnorm(length(ID), 0, sige)
    log_ca125.cs = cbind(1, age.long, screen_time) %*% betas + etas[1]*G.gas(TTs - screen_time, etas[2], etas[3]) + 
      rowSums(cbind(1, G.gas(TTs - screen_time, etas[2], etas[3])) * bb.long1) + ee.long1
  } else {
    betas = c(2.3, 0.0008, 0.01)
    etas = c(1.75, 1.26)
    sigb0 = exp(-0.74); sigb1 = exp(0.32); rhob = (exp(-0.59)-1)/(exp(-0.59)+1)
    SIGb = matrix(c(sigb0^2, sigb0*sigb1*rhob, sigb0*sigb1*rhob, sigb1^2), 2, 2)
    sige = exp(-1.45)
    
    bb.temp1 = rmvnorm(N, rep(0, 2), sigma = SIGb); bb.long1 = bb.temp1[ID, ]
    ee.long1 = rnorm(length(ID), 0, sige)
    log_ca125.cs = cbind(1, age.long, screen_time) %*% betas + etas[1]*G.lat(TTs - screen_time, etas[2]) + 
      rowSums(cbind(1, G.lat(TTs - screen_time, etas[2])) * bb.long1) + ee.long1
  }
  log_ca125[DD == 1] = log_ca125.cs[DD == 1]
  log_ca125 = as.vector(log_ca125)
  ### data generated
  data.temp = data.frame(cbind(ID = ID, 
                               Age = age.long, 
                               Screen_year = screen_time, 
                               DD_status = DD, 
                               Censor_year = TTs, 
                               log_CA125 = log_ca125))
  return(data.temp)
}

################################################################################
### simulate data from the conditional modeling approach under the biomarker independent censoring assumption
cm_ind_simu_data_func <- function(seed, kernel, N) {
  ### data generation function for conditional modeling under censoring dependent assumption
  ## kernel: kernel function for the conditional modeling
  ## N: sample size
  set.seed(seed)
  
  ###~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  ### age of case and control subjects
  # age.cs = rnorm(N.cs, mean = 63.5, sd = 5.6)
  # age.cn = rnorm(N.cn, mean = 62.3, sd = 5.4)
  age.probs = c(6.598482e-05, 3.299241e-05, 9.897724e-05, 9.722864e-02, 7.472781e-02, 6.426922e-02,
                5.730782e-02, 5.341471e-02, 7.423293e-02, 6.324645e-02, 6.172880e-02, 5.588915e-02,
                5.202903e-02, 4.942263e-02, 4.678324e-02, 4.378093e-02, 3.919499e-02, 3.681953e-02,
                3.467502e-02, 3.055097e-02, 2.652590e-02, 2.273177e-02, 1.517651e-02, 3.299241e-05,
                0, 0, 3.299241e-05)
  Age = sample(52:78, N, replace = T, prob = age.probs)
  
  ###~~~~~~~~~~~~~~~~~~~~~~~~~~~ survival time from a piecewise baseline hazard with baseline age as covariate
  t.knot = 2
  uu = runif(N, 0, 1)
  st = -log(uu)/exp(0.04*Age)/exp(-5.63114665)
  st[st > t.knot] = ((-log(uu)/exp(0.04*Age) - exp(-5.63114665)*t.knot)/exp(-5.85505853)+t.knot)[st > t.knot]
  
  ###~~~~~~~~~~~~~~~~~~~~~~~~~~~ censoring time
  # ct = pmin(rexp(N, rate = 0.08854268), 13)
  ct = pmin(rexp(N, rate = 1e-3), 13 + rnorm(N, 0, 0.1))
  
  ###~~~~~~~~~~~~~~~~~~~~~~~~~~~ observed survival time
  tts = pmin(st, ct)
  summary(tts)
  dd = ifelse(st < ct, 1, 0)
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('Generated cases and controls')
  print(table(dd))
  ni.temp = pmin(tts, 5)
  ni = unlist(sapply(ni.temp, function(x) length(0:x))) # cluster size
  
  ### data generated (long format)
  ID = rep(1:N, ni)
  age.long = rep(Age, ni) ## baseline age long format
  screen_time = unlist(sapply(ni.temp, function(x) {0:x})) # screening time (long format)
  DD = rep(dd, ni)
  TTs = rep(tts, ni)
  
  ### log_ca125 for case subjects
  if (kernel == 'exp') {
    betas = c(2.3, 0.0008, 0.007)
    etas = c(2.84, 1.97)
    sigb0 = exp(-0.73); sigb1 = exp(0.73); rhob = (exp(-0.58)-1)/(exp(-0.58)+1)
    SIGb = matrix(c(sigb0^2, sigb0*sigb1*rhob, sigb0*sigb1*rhob, sigb1^2), 2, 2)
    sige = exp(-1.44)
    
    bb.temp1 = rmvnorm(N, rep(0, 2), sigma = SIGb); bb.long1 = bb.temp1[ID, ]
    ee.long1 = rnorm(length(ID), 0, sige)
    log_ca125 = cbind(1, age.long, screen_time) %*% betas + etas[1]*G.exp(TTs - screen_time, etas[2]) + 
      rowSums(cbind(1, G.exp(TTs - screen_time, eta2 = etas[2])) * bb.long1) + ee.long1
  } else if (kernel == 'gas') {
    betas = c(2.3, 0.0008, 0.009)
    etas = c(6.8, -1.4, 2)
    sigb0 = exp(-0.74); sigb1 = exp(1.62); rhob = (exp(-0.58)-1)/(exp(-0.58)+1)
    SIGb = matrix(c(sigb0^2, sigb0*sigb1*rhob, sigb0*sigb1*rhob, sigb1^2), 2, 2)
    sige = exp(-1.44)
    
    bb.temp1 = rmvnorm(N, rep(0, 2), sigma = SIGb); bb.long1 = bb.temp1[ID, ]
    ee.long1 = rnorm(length(ID), 0, sige)
    log_ca125 = cbind(1, age.long, screen_time) %*% betas + etas[1]*G.gas(TTs - screen_time, etas[2], etas[3]) + 
      rowSums(cbind(1, G.gas(TTs - screen_time, etas[2], etas[3])) * bb.long1) + ee.long1
  } else {
    betas = c(2.3, 0.0008, 0.01)
    etas = c(1.75, 1.26)
    sigb0 = exp(-0.74); sigb1 = exp(0.32); rhob = (exp(-0.59)-1)/(exp(-0.59)+1)
    SIGb = matrix(c(sigb0^2, sigb0*sigb1*rhob, sigb0*sigb1*rhob, sigb1^2), 2, 2)
    sige = exp(-1.45)
    
    bb.temp1 = rmvnorm(N, rep(0, 2), sigma = SIGb); bb.long1 = bb.temp1[ID, ]
    ee.long1 = rnorm(length(ID), 0, sige)
    log_ca125 = cbind(1, age.long, screen_time) %*% betas + etas[1]*G.lat(TTs - screen_time, etas[2]) + 
      rowSums(cbind(1, G.lat(TTs - screen_time, etas[2])) * bb.long1) + ee.long1
  }
  log_ca125 = as.vector(log_ca125)
  ### data generated
  data.temp = data.frame(cbind(ID = ID, 
                               Age = age.long, 
                               Screen_year = screen_time, 
                               DD_status = DD, 
                               Censor_year = TTs, 
                               log_CA125 = log_ca125))
  return(data.temp)
  
}


################################################################################
### function to implement the conditional modeling approach, the joint modeling approach and 
### the landmark approach
cm_jm_lm_funcs <- function(training.dat, testing.dat, srt.time, wd.length) {
  #~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  ## training datasets for the conditional modeling
  training.dat.case = training.dat[training.dat$DD_status == 1, ]
  training.dat.case$ID = rep(1:length(unique(training.dat.case$ID)), times = table(training.dat.case$ID))
  training.dat.cons = training.dat[training.dat$DD_status == 0, ]
  training.dat.cons$ID = rep(1:length(unique(training.dat.cons$ID)), times = table(training.dat.cons$ID))
  # training dataset for the landmark method
  LM.training.dat = cutdata_func(training.dat, srt.time = srt.time, wd.length = wd.length)
  
  ## number of cases and controls in the training samples
  print(table(LM.training.dat$DD_status))
  
  
  #~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  testing.dat.used = NULL
  for (ids in unique(testing.dat$ID)) {
    temp.test = testing.dat[testing.dat$ID == ids, ]
    ### remove subjects who did not survival after the landmark time srt.time
    if (max(temp.test$Censor_year) >= srt.time) {
      temp.test = temp.test[temp.test$Screen_year <= srt.time, ] ## only keep observations observed before srt.time
    } else {
      temp.test = NULL
    }
    testing.dat.used = rbind(testing.dat.used, temp.test)
  }
  testing.dat.used$TT_new = ifelse(testing.dat.used$Censor_year <= srt.time + wd.length, 
                                   testing.dat.used$Censor_year, srt.time + wd.length)
  testing.dat.used$DD_new = ifelse(testing.dat.used$Censor_year <= srt.time + wd.length, 
                                   testing.dat.used$DD_status, 0)
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print(paste('Total subjects in testing data: ', length(unique(testing.dat.used$ID)), sep = ""))
  
  ## testing dataset for the landmarking method
  LM.testing.dat = cutdata_func(testing.dat, srt.time = srt.time, wd.length = wd.length)
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print(paste('Total number of subjects in the testing data: ', length(unique(testing.dat$ID)), sep = ''))
  print(paste('Total number of case subjects in the testing data: ',
              length(which(sapply(split(testing.dat$DD_status, testing.dat$ID), min) == 1)), sep = ''))
  print(paste('Total number of control subjects in the testing data: ',
              length(which(sapply(split(testing.dat$DD_status, testing.dat$ID), min) == 0)), sep = ''))
  
  print(paste('Total number of subjects in the used testing data: ', length(LM.testing.dat$ID), sep = ''))
  print(paste('Total number of case (original) subjects in the used testing data: ',
              length(which(LM.testing.dat$DD_status == 1)), sep = ''))
  print(paste('Total number of control (original) subjects in the used testing data: ',
              length(which(LM.testing.dat$DD_status == 0)), sep = ''))
  print(paste('Total number of case (modified) subjects in the used testing data: ',
              length(which(LM.testing.dat$DD_new == 1)), sep = ''))
  print(paste('Total number of control (modified) subjects in the used testing data: ',
              length(which(LM.testing.dat$DD_new == 0)), sep = ''))
  
  #~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  #### survival data for coxph
  temp.surv = training.dat[!duplicated(training.dat$ID), ]
  
  ##################################################################################################
  ## implement joint modeling
  ## sub-lme model 
  lme1 = lme(log_CA125 ~ Age + Screen_year, random = ~ Screen_year | ID, data = training.dat,
             control = lmeControl(maxIter = 10000, opt = 'optim', optimMethod = 'SANN'))
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('Estimation for lme1 under joint modeling: ')
  print(summary(lme1))
  
  ## sub survival model
  cox.model = coxph(Surv(Censor_year, DD_status) ~ Age, data = temp.surv, x = TRUE)
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('Estimation for Cox PH under joint modeling: ')
  print(summary(cox.model))
  
  ## joint modeling approach
  ## use current value + current slope
  dform_both1 = list(fixed = ~ 1, indFixed = 3, random = ~ 1, indRandom = 2)
  joint12 = jointModel(lme1, cox.model, timeVar = 'Screen_year', parameterization = 'both',
                       derivForm = dform_both1, method = 'piecewise-PH-aGH', control = list(lng.in.kn = 1))
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('Estimation for joint12 under joint modeling: ')
  print(summary(joint12))
  
  ####################################################################################################
  ### fit coxph using LM.training.dat
  LM.coxph1 = coxph(Surv(TT_new, DD_new) ~ Age + log_CA125, data = LM.training.dat, method = 'breslow')
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('Coxph1 for landmarking method:')
  print(LM.coxph1)
  
  ### predict subject-specific survival probabilities using LM.testing.dat
  LM.survfit1 = survfit(LM.coxph1, newdata = LM.testing.dat)
  LM.surv.probs1 = 1 - LM.survfit1$surv[nrow(LM.survfit1$surv), ]
  
  ####################################################################################################
  ### model fitting and risk calculation using conditional modeling approaches
  #### estimate CM with exponential kernel for cases
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('CM with exponential kernel:')
  th.exp = c(2.3, 0.0008, 0.007, 2.8, 1.9, -0.73, 0.73, -0.6, -1.4)
  fit.exp = optim(fn = loglik.exp,
                  par = th.exp,
                  YY = training.dat.case$log_CA125,
                  TIME = training.dat.case$Screen_year,
                  Xmat = as.matrix(cbind(1, training.dat.case$Age, training.dat.case$Screen_year)),
                  Tlong = training.dat.case$Censor_year,
                  ID = training.dat.case$ID,
                  method = "BFGS", hessian = F, control = list(trace = T, maxit = 1e4))
  print(fit.exp)
  
  #### estimate CM with Gaussian kernel for cases
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('CM with Gaussian kernel:')
  th.gas = c(2.25, 0.002, 0.01, 5, -1.0, 1.6, -0.7, 1.2, -0.7, -1.4)
  fit.gas = optim(fn = loglik.gas,
                  par = th.gas,
                  YY = training.dat.case$log_CA125,
                  TIME = training.dat.case$Screen_year,
                  Xmat = as.matrix(cbind(1, training.dat.case$Age, training.dat.case$Screen_year)),
                  Tlong = training.dat.case$Censor_year,
                  ID = training.dat.case$ID,
                  method = "BFGS", hessian = F, control = list(trace = T, maxit = 1e4))
  print(fit.gas)
  
  #### estimate CM with latent changepoint kernel for cases
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('CM with latent changepoint kernel:')
  th.lat = c(2.3, 0.0008, 0.01, 1.8, 1.3, -0.73,  0.32, -0.6, -1.4)
  fit.lat = optim(fn = loglik.lat,
                  par = th.lat,
                  YY = training.dat.case$log_CA125,
                  TIME = training.dat.case$Screen_year,
                  Xmat = cbind(1, training.dat.case$Age, training.dat.case$Screen_year),
                  Tlong = training.dat.case$Censor_year,
                  ID = training.dat.case$ID,
                  method = "BFGS", hessian = F, control = list(trace = T, maxit = 1e4))
  print(fit.lat)
  
  #### estimate the control model
  fit.con0 = lme(log_CA125 ~ Age + Screen_year, random = ~ Screen_year|ID, data = training.dat.cons)
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('Control model0 fitting under conditional modeling:')
  print(summary(fit.con0))
  
  TT = c(sapply(split(training.dat$Censor_year, training.dat$ID), 'max')) ### observed survival time, since randomization
  SS = sapply(split(training.dat$DD_status, training.dat$ID), max) ### disease status
  #### censoring distribution
  KM.C = survfit(Surv(TT, 1 - SS) ~ 1)
  # KM.C1 = survfit(Surv(TT, 1 - SS) ~ age_training + yy)
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('Censoring distribution:')
  print((KM.C))
  
  #### survival distribution
  age_training = sapply(split(training.dat$Age, training.dat$ID), 'max')
  Wmat = cbind(age_training)
  lam.knot = c(2) # 2 is chosen due to the minimum likelihood value
  thS = c(0.03824139, -6.63114665, -6.85505853)
  fitS = optim(fn = pwcPHlik,
               par = thS,
               TT = TT, DT = SS, Wmat = Wmat, lam.knot = lam.knot,
               method = "BFGS", hessian = F, control = list(trace = T, maxit = 1e4))
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('Survival density function:')
  print(fitS)
  
  th.exp.cs = as.vector(fit.exp$par)
  th.gas.cs = as.vector(fit.gas$par)
  th.lat.cs = as.vector(fit.lat$par)
  th.cn.fixed = as.vector(fit.con0$coefficients$fixed)
  temp.rand.mat0 = getVarCov(fit.con0, 'random.effects')
  th.cn.random = c(as.vector(sqrt(diag(temp.rand.mat0))), cov2cor(temp.rand.mat0)[2, 1], fit.con0$sigma)
  th.surv = as.vector(fitS$par)
  
  #### calculate risks using CM
  dd = (unique(testing.dat.used$ID))
  jm12.risks = risk.CM.exp0 = risk.CM.gas0 = risk.CM.lat0 = temp.cm.exp.ind = 
    temp.cm.gas.ind = temp.cm.lat.ind = rep(NA, length(dd))
  ####################################################################################################
  ## calculate subject-specific risks using joint models
  
  for (k in 1:length(dd)) {
    id = unique(testing.dat.used$ID)[k]
    mynewdat = testing.dat.used[testing.dat.used$ID == id, ]
    jm12.risks[k] = 1 - survfitJM(joint12, newdata = mynewdat, idVar = 'ID', survTimes = srt.time + wd.length,
                                  last.time = srt.time)$summaries[[1]][2]
    loc = which(testing.dat.used$ID == id)
    Yi = testing.dat.used$log_CA125[loc]
    tij = testing.dat.used$Screen_year[loc]
    Xi.mat = matrix(cbind(1, testing.dat.used$Age, testing.dat.used$Screen_year)[loc, ], ncol = 3) ### design matrix for fixed effects in the case model
    Wi.mat = cbind(testing.dat.used$Age[loc][1]) ### design matrix for the survival function
    X0i.mat0 = matrix(cbind(1, testing.dat.used$Age, testing.dat.used$Screen_year)[loc, ], ncol = 3)
    Z0i.mat0 = matrix(cbind(1, testing.dat.used$Screen_year)[loc, ], ncol = 2)
    
    #### CM under independent censoring assumption
    tryCatch({temp.cm.exp.ind[k] = plogis(pred.exp.ind(th1 = c(th.exp.cs, th.surv),
                                                       Yi = Yi,
                                                       tij = tij,
                                                       Xi.mat = Xi.mat,
                                                       Wi.mat = Wi.mat,
                                                       lam.knot = lam.knot,
                                                       tstart = srt.time, 
                                                       pred.gap = wd.length))}, 
             error = function(e){})
    tryCatch({temp.cm.gas.ind[k] = plogis(pred.gas.ind(th1 = c(th.gas.cs, th.surv),
                                                       Yi = Yi,
                                                       tij = tij,
                                                       Xi.mat = Xi.mat,
                                                       Wi.mat = Wi.mat,
                                                       lam.knot = lam.knot,
                                                       tstart = srt.time, 
                                                       pred.gap = wd.length))}, 
             error = function(e){})
    tryCatch({temp.cm.lat.ind[k] = plogis(pred.lat.ind(th1 = c(th.lat.cs, th.surv),
                                                       Yi = Yi,
                                                       tij = tij,
                                                       Xi.mat = Xi.mat,
                                                       Wi.mat = Wi.mat,
                                                       lam.knot = lam.knot,
                                                       tstart = srt.time, 
                                                       pred.gap = wd.length))}, 
             error = function(e){})
    
    ### CM with exponential kernel
    tryCatch({risk.CM.exp0[k] = plogis(pred.exp.dep(th1 = c(th.exp.cs, th.cn.fixed, th.cn.random, th.surv),
                                                    Yi = Yi,
                                                    tij = tij,
                                                    Xi.mat = Xi.mat,
                                                    Wi.mat = Wi.mat,
                                                    X0i.mat = X0i.mat0,
                                                    Z0i.mat = Z0i.mat0,
                                                    lam.knot = lam.knot,
                                                    tstart = srt.time,
                                                    pred.gap = wd.length,
                                                    KM.C = KM.C, 
                                                    is.true = F))},
             error = function(e){})
    
    ### CM with Gaussian kernel
    tryCatch({risk.CM.gas0[k] = plogis(pred.gas.dep(th1 = c(th.gas.cs, th.cn.fixed, th.cn.random, th.surv),
                                                    Yi = Yi,
                                                    tij = tij,
                                                    Xi.mat = Xi.mat,
                                                    Wi.mat = Wi.mat,
                                                    X0i.mat = X0i.mat0,
                                                    Z0i.mat = Z0i.mat0,
                                                    lam.knot = lam.knot,
                                                    tstart = srt.time,
                                                    pred.gap = wd.length,
                                                    KM.C = KM.C, 
                                                    is.true = F))},
             error = function(e){})
    
    ### CM with latent changepoint kernel
    tryCatch({risk.CM.lat0[k] = plogis(pred.lat.dep(th1 = c(th.lat.cs, th.cn.fixed, th.cn.random, th.surv),
                                                    Yi = Yi,
                                                    tij = tij,
                                                    Xi.mat = Xi.mat,
                                                    Wi.mat = Wi.mat,
                                                    X0i.mat = X0i.mat0,
                                                    Z0i.mat = Z0i.mat0,
                                                    lam.knot = lam.knot,
                                                    tstart = srt.time,
                                                    pred.gap = wd.length,
                                                    KM.C = KM.C, 
                                                    is.true = F))},
             error = function(e){})
    print(k)
  }
  
  #### output
  output = data.frame(cbind(ID = unique(testing.dat.used$ID), 
                            DD_status = sapply(split(testing.dat.used$DD_status, testing.dat.used$ID), min), 
                            DD_new = sapply(split(testing.dat.used$DD_new, testing.dat.used$ID), min), 
                            Screen_year = sapply(split(testing.dat.used$Screen_year, testing.dat.used$ID), max), 
                            TT_new = sapply(split(testing.dat.used$TT_new, testing.dat.used$ID), min),
                            Censor_year = sapply(split(testing.dat.used$Censor_year, testing.dat.used$ID), min), 
                            Age = sapply(split(testing.dat.used$Age, testing.dat.used$ID), min), 
                            risk.JM12 = jm12.risks,
                            risk.LM1 = LM.surv.probs1,
                            risk.CM.exp0 = risk.CM.exp0,
                            risk.CM.gas0 = risk.CM.gas0,
                            risk.CM.lat0 = risk.CM.lat0,
                            risk.CM.exp.ind = temp.cm.exp.ind, 
                            risk.CM.gas.ind = temp.cm.gas.ind, 
                            risk.CM.lat.ind = temp.cm.lat.ind))
  
  ####################################################################################################
  ### calculate time-dependent time-AUC for all methods
  nobs = nrow(output)
  tauc_jm12 = survivalROC.C(Stime = output$Censor_year,
                            status = output$DD_status,
                            marker = output$risk.JM12,
                            predict.time = wd.length + srt.time,
                            span = 0.25*nobs^(-0.20))$AUC
  tauc_lm1 = survivalROC.C(Stime = output$Censor_year,
                           status = output$DD_status,
                           marker = output$risk.LM1,
                           predict.time = wd.length + srt.time,
                           span = 0.25*nobs^(-0.20))$AUC
  tauc_cm_exp0 = survivalROC.C(Stime = output$Censor_year,
                               status = output$DD_status,
                               marker = output$risk.CM.exp0,
                               predict.time = wd.length + srt.time,
                               span = 0.25*nobs^(-0.20))$AUC
  tauc_cm_gas0 = survivalROC.C(Stime = output$Censor_year,
                               status = output$DD_status,
                               marker = output$risk.CM.gas0,
                               predict.time = wd.length + srt.time,
                               span = 0.25*nobs^(-0.20))$AUC
  tauc_cm_lat0 = survivalROC.C(Stime = output$Censor_year,
                               status = output$DD_status,
                               marker = output$risk.CM.lat0,
                               predict.time = wd.length + srt.time,
                               span = 0.25*nobs^(-0.20))$AUC
  tauc_cm_exp_ind = survivalROC.C(Stime = output$Censor_year,
                                  status = output$DD_status,
                                  marker = output$risk.CM.exp.ind,
                                  predict.time = wd.length + srt.time,
                                  span = 0.25*nobs^(-0.20))$AUC
  
  tauc_cm_gas_ind = survivalROC.C(Stime = output$Censor_year,
                                  status = output$DD_status,
                                  marker = output$risk.CM.gas.ind,
                                  predict.time = wd.length + srt.time,
                                  span = 0.25*nobs^(-0.20))$AUC
  
  tauc_cm_lat_ind = survivalROC.C(Stime = output$Censor_year,
                                  status = output$DD_status,
                                  marker = output$risk.CM.lat.ind,
                                  predict.time = wd.length + srt.time,
                                  span = 0.25*nobs^(-0.20))$AUC
  
  myresults = data.frame(cbind(srt.time = srt.time, 
                               wd.length = wd.length,
                               tauc_jm12 = tauc_jm12,
                               tauc_lm1 = tauc_lm1,
                               tauc_cm_exp0 = tauc_cm_exp0,
                               tauc_cm_gas0 = tauc_cm_gas0,
                               tauc_cm_lat0 = tauc_cm_lat0,
                               tauc_cm_exp_ind = tauc_cm_exp_ind, 
                               tauc_cm_gas_ind = tauc_cm_gas_ind, 
                               tauc_cm_lat_ind = tauc_cm_lat_ind))
  print('~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~')
  print('time-dependent AUCs')
  print(myresults)
  return(myresults)
}

################################################################################
### simulation when the conditional modeling approach is the true model
cm_simu_risk_func <- function(n.sims, seed, srt.time, wd.length, kernel, N, censor_assumption) {
  ## n.sims: number of simulations
  ## seed: seed 
  ## srt.time: landmarking time or starting time
  ## wd.length: length of prediction window
  ## kernel: kernel used for the conditional modeling approach: exp, gas, and lat, meaning exponential, Gaussian, and latent changepoint kernels
  ## N: sample size
  ## censor_assumption: dependent or independent assumption
  set.seed(seed) 
  
  if (censor_assumption == 'ind') {
    training.dat = cm_ind_simu_data_func(seed = seed, kernel = kernel, N = N)
    testing.dat = cm_ind_simu_data_func(seed = seed + 2e6, kernel = kernel, N = N)
  } else {
    training.dat = cm_dep_simu_data_func(seed = seed, kernel = kernel, N = N)
    testing.dat = cm_dep_simu_data_func(seed = seed + 2e6, kernel = kernel, N = N)
  }
  mytauc = cm_jm_lm_funcs(training.dat = training.dat, testing.dat = testing.dat, srt.time, wd.length)
  
  return(mytauc)
}

################################################################################

### run a simulation 

sim_result = cm_simu_risk_func(n.sims = 1,
                               seed = 1,
                               srt.time = 5,
                               wd.length = 2,
                               kernel = 'exp',
                               N = 1e3,
                               censor_assumption = 'dep')

################################################################################