################################################################################
# Revised reverse causation simulation: main analysis, four original sensitivity
# analyses, and mortality / competing-death sensitivity analysis.
################################################################################

suppressPackageStartupMessages({
  library(survival)
  library(ggplot2)
})

args <- commandArgs(trailingOnly = TRUE)
N_REPS <- 500L
N_POP  <- 5000L
OUT_DIR <- '/Users/jwang30/Postdoc/Research/Reverse MR/Code/IJE'
BMI_ERROR_SD <- 1
RUN_PRIMARY <- TRUE
RUN_MORTALITY <- TRUE
ENTRY_AGES <- seq(45L, 80L, 5L)
STOP_AGE <- 90L
stopifnot(N_REPS >= 1L, N_POP >= 100L)
dir.create(OUT_DIR, showWarnings = FALSE, recursive = TRUE)
FIG_DIR <- file.path(OUT_DIR, "figures")
dir.create(FIG_DIR, showWarnings = FALSE, recursive = TRUE)

# SAME fixed y-axis range across each figure/panel and across HR figures.
# This is increased automatically, if needed, to avoid clipping an estimate.
MIN_HR_YLIM <- c(0.65, 1.3)

# ---------------------------------------------------------------------------
# 1. Explicit parameters; revisions to Equations (1) and (3)
# ---------------------------------------------------------------------------
# educ=1: college education; educ=0: no college education.
# Referee 3 correction: latent AD education coefficient -0.3 
# and BMI +1.2*(1-educ), so persons without a college degree have higher BMI.
# All 5 no-mortality scenarios use these corrections.
SCENARIOS <- list(
  primary = list(label = "Primary", bmi_intercept = 27, age_quadratic = -0.004,
                 latent_bmi_coef = -0.5, U_AD = 0.05, U_BMI = 0.1,
                 p_female = 0.5, p_college = 0.4, C_sd = 3),
  s1 = list(label = "Weaker preclinical AD effect on BMI",
            bmi_intercept = 27, age_quadratic = -0.004,
            latent_bmi_coef = -0.2, U_AD = 0.05, U_BMI = 0.1,
            p_female = 0.5, p_college = 0.4, C_sd = 3),
  s2 = list(label = "Flatter BMI trajectory",
            bmi_intercept = 27, age_quadratic = -0.002,
            latent_bmi_coef = -0.5, U_AD = 0.05, U_BMI = 0.1,
            p_female = 0.5, p_college = 0.4, C_sd = 3),
  s3 = list(label = "No unmeasured confounding",
            bmi_intercept = 27, age_quadratic = -0.004,
            latent_bmi_coef = -0.5, U_AD = 0, U_BMI = 0,
            p_female = 0.5, p_college = 0.4, C_sd = 3),
  s4 = list(label = "Alternative confounder distributions",
            bmi_intercept = 27, age_quadratic = -0.004,
            latent_bmi_coef = -0.5, U_AD = 0.05, U_BMI = 0.1,
            p_female = 0.7, p_college = 0.2, C_sd = 2)
)

latent_AD <- function(age, pop, cfg) {
  d <- pmax(age - 45, 0)
  gamma_age <- (0.0015 * d + 0.00015 * d^2) * 2
  -10.5 + 0.09 * age + gamma_age * pop$G +
    0.5 * pop$sex - 0.3 * pop$educ +
    cfg$U_AD * pop$U + 0.05 * pop$C
}

AD_hazard <- function(age, pop, cfg, BMI_z, HR_BMI) {
  p0 <- plogis(latent_AD(age, pop, cfg))
  h0 <- -log1p(-pmin(p0, 1 - 1e-12))
  h0 * exp(log(HR_BMI) * BMI_z)
}

BMI_mean <- function(age, pop, cfg) {
  latent <- latent_AD(age, pop, cfg)
  bmi <- cfg$bmi_intercept + cfg$latent_bmi_coef * latent +
    cfg$age_quadratic * (age - 55)^2 + 1.5 * pop$sex +
    1.2 * (1 - pop$educ) + 1.0 * pop$C + cfg$U_BMI * pop$U
  pmax(pmin(bmi, 55), 15)
}

make_population <- function(n, seed, cfg, persistent_error = FALSE) {
  set.seed(seed)
  pop <- data.frame(
    ID = seq_len(n), G = rnorm(n),
    sex = rbinom(n, 1L, cfg$p_female),
    educ = rbinom(n, 1L, cfg$p_college),
    C = rnorm(n, 0, cfg$C_sd),
    U = rnorm(n, 0, 1)
  )
  if (persistent_error) pop$bmi_error <- rnorm(n, 0, BMI_ERROR_SD)
  pop
}

extract_cox <- function(dat, exposure, HR_BMI) {
  var <- if (exposure == "BMI") "BMI_z" else "obese"
  if (nrow(dat) < 30L || sum(dat$AD) < 5L ||
      length(unique(dat[[var]])) < 2L) return(NULL)
  formula <- if (exposure == "BMI") {
    Surv(fu, AD) ~ BMI_z + sex + educ + C
  } else {
    Surv(fu, AD) ~ obese + sex + educ + C
  }
  fit <- tryCatch(suppressWarnings(coxph(formula, data = dat, ties = "efron")),
                  error = function(e) NULL)
  if (is.null(fit) || !var %in% names(coef(fit))) return(NULL)
  b <- unname(coef(fit)[var])
  se <- tryCatch(sqrt(unname(vcov(fit)[var, var])), error = function(e) NA_real_)
  if (!is.finite(b) || !is.finite(se)) return(NULL)
  data.frame(exposure = exposure, logHR = b, selogHR = se,
             HR = exp(b),
             RHR = if (exposure == "BMI") exp(b) / HR_BMI else NA_real_)
}

# ---------------------------------------------------------------------------
# 2. No-mortality primary + existing sensitivity analyses
# ---------------------------------------------------------------------------

run_primary_rep <- function(n, seed, cfg, HR_BMI) {
  pop <- make_population(n, seed, cfg)
  out <- vector("list", 2L * length(ENTRY_AGES))
  diag <- vector("list", length(ENTRY_AGES))
  k_out <- 0L
  for (i in seq_along(ENTRY_AGES)) {
    bage <- ENTRY_AGES[i]
    bmi <- BMI_mean(bage, pop, cfg) + rnorm(n, 0, BMI_ERROR_SD)
    bmi_sd <- sd(bmi)
    if (!is.finite(bmi_sd) || bmi_sd <= 0) stop("Nonpositive BMI SD")
    z <- (bmi - mean(bmi)) / bmi_sd
    obese <- as.integer(bmi >= 30)
    admin <- pmin(round(runif(n, 1, 29)), STOP_AGE - bage)
    fu <- admin
    AD <- integer(n)
    for (year in seq_len(max(admin))) {
      at_risk <- which(AD == 0L & admin >= year)
      if (!length(at_risk)) next
      h_AD <- AD_hazard(bage + year, pop[at_risk, , drop = FALSE],
                        cfg, z[at_risk], HR_BMI)
      newly <- at_risk[runif(length(at_risk)) < -expm1(-h_AD)]
      if (length(newly)) {
        AD[newly] <- 1L
        fu[newly] <- year
      }
    }
    dat <- data.frame(fu = fu, AD = AD, BMI_z = z, obese = obese,
                      sex = pop$sex, educ = pop$educ, C = pop$C)
    stopifnot(all(dat$fu > 0), all(dat$fu <= 90 - bage))
    for (exposure in c("BMI", "Obesity")) {
      fitted <- extract_cox(dat, exposure, HR_BMI)
      if (is.null(fitted)) next
      k_out <- k_out + 1L
      fitted$baseline_age <- bage
      fitted$HR_BMI <- HR_BMI
      out[[k_out]] <- fitted
    }
    diag[[i]] <- data.frame(baseline_age = bage, HR_BMI = HR_BMI,
                            n_eligible = n, n_AD_followup = sum(AD),
                            mean_followup = mean(fu), mean_BMI = mean(bmi),
                            sd_BMI = bmi_sd, pct_obese = mean(obese))
  }
  list(estimates = do.call(rbind, Filter(Negate(is.null), out)),
       diagnostics = do.call(rbind, diag))
}

# ---------------------------------------------------------------------------
# 3. Mortality model (sensitivity only)
# ---------------------------------------------------------------------------
# NCHS U.S. life table (2024), five-year q(x,x+5), ages 45-89, both sexes.
# Original source: https://www.cdc.gov/nchs/data/nvsr/nvsr75/nvsr75-05.pdf
# These are baseline mortality hazard ANCHORS, not exact calibrated marginal
# death probabilities after covariate multipliers are included.
LIFE_TABLE <- data.frame(
  age_start = seq(45L, 85L, 5L),
  q5 = c(0.015736, 0.022552, 0.033316, 0.050357, 0.071930,
         0.102345, 0.158277, 0.257987, 0.410387)
)
LIFE_TABLE$annual_hazard <- -log(1 - LIFE_TABLE$q5) / 5

# per 5 BMI units (Global BMI Mortality Collaboration, Lancet 2016).
MORT <- list(bmi_hr_per_5 = 1.30, preAD_hr_per_unit = 1.10,
             C_hr_per_sd = 1.10, U_hr_per_sd = 1.10, female_hr = 0.80,
             positive_interaction_hr = 4.0)

MORTALITY_MODES <- c("none", "mortality", "mortality_positive_interaction")
MORTALITY_LABELS <- c("No mortality", "Mortality: no interaction",
                      "Mortality: positive interaction")

get_BMI_at_age <- function(age, pop, cfg) {
  BMI_mean(age, pop, cfg) + pop$bmi_error
}

death_hazard <- function(age, subpop, cfg, mode) {
  if (!mode %in% MORTALITY_MODES) stop("Unknown mortality mode: ", mode)
  if (mode == "none") return(rep(0, nrow(subpop)))
  band <- floor((age - 45) / 5) + 1L
  base <- LIFE_TABLE$annual_hazard[band]
  prior_bmi <- get_BMI_at_age(age, subpop, cfg)
  preAD <- latent_AD(age, subpop, cfg)
  center_preAD <- -10.5 + 0.09 * (age + 1)
  eta <- log(MORT$bmi_hr_per_5) * ((pmax(prior_bmi - 25, 0) - 2) / 5) +
    log(MORT$preAD_hr_per_unit) * (preAD - center_preAD) +
    log(MORT$C_hr_per_sd) * subpop$C / 3 +
    log(MORT$U_hr_per_sd) * subpop$U +
    log(MORT$female_hr) * (subpop$sex - 0.5)
  
  # Additional positive joint effect on the *mortality hazard* only.
  # It is active only when BMI > 25 AND the latent preclinical AD score is
  # above the original age-specific reference value. Main effects and
  # centering in the original mortality model are unchanged.
  if (mode == "mortality_positive_interaction") {
    bmi_excess <- pmax(prior_bmi - 25, 0) / 5
    preAD_excess <- pmax(preAD - center_preAD, 0)
    eta <- eta + log(MORT$positive_interaction_hr) * bmi_excess * preAD_excess
  }
  
  base * exp(pmin(eta, 15))
}

# Cause-specific exponential hazards yield mutually exclusive AD and death
# events in each year; without mortality this is Bernoulli(1-exp(-ad_h)).
draw_competing_events <- function(ad_h, h_death) {
  h <- ad_h + h_death
  p_any <- -expm1(-h)
  p_AD <- ifelse(h > 0, p_any * ad_h / h, 0)
  p_death <- ifelse(h > 0, p_any * h_death / h, 0)
  u <- runif(length(ad_h))
  ifelse(u < p_AD, 1L, ifelse(u < p_AD + p_death, 2L, 0L))
}


prebaseline_histories <- function(pop, cfg, HR_BMI, mode) {
  n <- nrow(pop)
  first_type <- integer(n) # 0 alive and AD-free, 1 AD, 2 death
  event_age <- rep(Inf, n)
  for (a in 45:79) {
    idx <- which(first_type == 0L)
    if (!length(idx)) break
    pp <- pop[idx, , drop = FALSE]
    next_bmi <- get_BMI_at_age(a + 1L, pp, cfg)
    z <- (next_bmi - mean(next_bmi)) / sd(next_bmi)
    h_AD <- AD_hazard(a + 1L, pp, cfg, z, HR_BMI)
    dh <- death_hazard(a, pp, cfg, mode)
    events <- draw_competing_events(h_AD, dh)
    hit <- which(events != 0L)
    if (length(hit)) {
      first_type[idx[hit]] <- events[hit]
      event_age[idx[hit]] <- a + 1L
    }
  }
  data.frame(event_type = first_type, event_age = event_age)
}

run_mortality_cohort <- function(pop, history, cfg, bage, HR_BMI, mode) {
  eligible <- history$event_age > bage
  idx <- which(eligible)
  n <- length(idx)
  diag <- data.frame(baseline_age = bage, HR_BMI = HR_BMI,
                     mode = mode, source_n_age45 = nrow(pop),
                     n_prior_AD = sum(history$event_type == 1L & !eligible),
                     n_prior_death = sum(history$event_type == 2L & !eligible),
                     n_eligible = n,
                     proportion_eligible = mean(eligible),
                     n_AD_followup = NA_integer_,
                     n_death_followup = NA_integer_,
                     mean_followup = NA_real_, mean_BMI = NA_real_,
                     sd_BMI = NA_real_)
  if (n < 30L) return(list(estimates = NULL, diagnostics = diag))
  pp <- pop[idx, , drop = FALSE]
  bmi <- get_BMI_at_age(bage, pp, cfg)
  bmi_sd <- sd(bmi)
  if (!is.finite(bmi_sd) || bmi_sd <= 0) return(list(estimates = NULL, diagnostics = diag))
  z <- (bmi - mean(bmi)) / bmi_sd
  obese <- as.integer(bmi >= 30)
  admin <- pmin(round(runif(n, 1, 29)), STOP_AGE - bage)
  fu <- admin
  type <- integer(n)
  for (year in seq_len(max(admin))) {
    active <- which(type == 0L & admin >= year)
    if (!length(active)) next
    at_risk <- pp[active, , drop = FALSE]
    h_AD <- AD_hazard(bage + year, at_risk, cfg, z[active], HR_BMI)
    h_death <- death_hazard(bage + year - 1L, at_risk, cfg, mode)
    ev <- draw_competing_events(h_AD, h_death)
    hits <- which(ev != 0L)
    if (length(hits)) {
      type[active[hits]] <- ev[hits]
      fu[active[hits]] <- year
    }
  }
  diag$n_AD_followup <- sum(type == 1L)
  diag$n_death_followup <- sum(type == 2L)
  diag$mean_followup <- mean(fu)
  diag$mean_BMI <- mean(bmi)
  diag$sd_BMI <- bmi_sd
  dat <- data.frame(fu = fu, AD = as.integer(type == 1L), BMI_z = z,
                    obese = obese, sex = pp$sex, educ = pp$educ, C = pp$C)
  stopifnot(all(dat$fu > 0), all(dat$fu <= 90 - bage))
  results <- lapply(c("BMI", "Obesity"), function(exposure) {
    fitted <- extract_cox(dat, exposure, HR_BMI)
    if (is.null(fitted)) return(NULL)
    fitted$baseline_age <- bage
    fitted$HR_BMI <- HR_BMI
    fitted$mode <- mode
    fitted$n_eligible <- n
    fitted$n_AD <- sum(type == 1L)
    fitted$n_death <- sum(type == 2L)
    fitted
  })
  list(estimates = do.call(rbind, Filter(Negate(is.null), results)),
       diagnostics = diag)
}

# ---------------------------------------------------------------------------
# 4. Run and write all simulations
# ---------------------------------------------------------------------------
PRIMARY_EST <- NULL
PRIMARY_DIAG <- NULL
if (RUN_PRIMARY) {
  primary_est_list <- list()
  primary_diag_list <- list()
  k <- 0L
  for (sname in names(SCENARIOS)) {
    cfg <- SCENARIOS[[sname]]
    for (r in seq_len(N_REPS)) {
      for (truth in c(1, 1.3)) {
        # Same seed for both causal truths: common source covariates/error draws
        result <- run_primary_rep(N_POP, 10000L + r, cfg, truth)
        k <- k + 1L
        if (!is.null(result$estimates)) {
          result$estimates$replication <- r
          result$estimates$scenario <- sname
          primary_est_list[[k]] <- result$estimates
        }
        result$diagnostics$replication <- r
        result$diagnostics$scenario <- sname
        primary_diag_list[[k]] <- result$diagnostics
      }
      if (r == 1L || r %% 25L == 0L || r == N_REPS)
        message("Main scenario ", sname, ": replication ", r, "/", N_REPS)
    }
  }
  PRIMARY_EST <- do.call(rbind, primary_est_list)
  PRIMARY_DIAG <- do.call(rbind, primary_diag_list)
  rownames(PRIMARY_EST) <- NULL
  write.csv(PRIMARY_EST, file.path(OUT_DIR, "primary_all_replication_estimates.csv"), row.names = FALSE)
  write.csv(PRIMARY_DIAG, file.path(OUT_DIR, "primary_diagnostics.csv"), row.names = FALSE)
}

MORT_EST <- NULL
MORT_DIAG <- NULL
if (RUN_MORTALITY) {
  mortality_est_list <- list()
  mortality_diag_list <- list()
  k <- 0L
  cfg <- SCENARIOS$primary
  for (r in seq_len(N_REPS)) {
    pop <- make_population(N_POP, 800000L + r, cfg, persistent_error = TRUE)
    for (truth in c(1, 1.3)) {
      for (mode in MORTALITY_MODES) {
        set.seed(2000000L + 1000L * r +
                   (if (truth == 1) 13L else 41L))
        history <- prebaseline_histories(pop, cfg, truth, mode)
        for (bage in ENTRY_AGES) {
          k <- k + 1L
          ans <- run_mortality_cohort(pop, history, cfg, bage, truth, mode)
          if (!is.null(ans$estimates)) {
            ans$estimates$replication <- r
            mortality_est_list[[k]] <- ans$estimates
          }
          ans$diagnostics$replication <- r
          mortality_diag_list[[k]] <- ans$diagnostics
        }
      }
    }
    if (r == 1L || r %% 25L == 0L || r == N_REPS)
      message("Mortality extension: replication ", r, "/", N_REPS)
  }
  MORT_EST <- do.call(rbind, Filter(Negate(is.null), mortality_est_list))
  MORT_DIAG <- do.call(rbind, mortality_diag_list)
  if (is.null(MORT_EST)) stop("No mortality model estimates: review sample size and events")
  rownames(MORT_EST) <- NULL
  write.csv(MORT_EST, file.path(OUT_DIR, "mortality_all_replication_estimates.csv"), row.names = FALSE)
  write.csv(MORT_DIAG, file.path(OUT_DIR, "mortality_cohort_diagnostics.csv"), row.names = FALSE)
  write.csv(LIFE_TABLE, file.path(OUT_DIR, "mortality_life_table_anchors.csv"), row.names = FALSE)
  write.csv(data.frame(parameter = names(MORT), value = unlist(MORT)),
            file.path(OUT_DIR, "mortality_assumed_parameters.csv"), row.names = FALSE)
}

# ---------------------------------------------------------------------------
# 5. Monte Carlo summaries (geometric mean HR and interval on log HR scale)
# ---------------------------------------------------------------------------
summarize_mc <- function(est, keys) {
  splits <- split(est, interaction(est[keys], drop = TRUE, lex.order = TRUE))
  parts <- lapply(splits, function(d) {
    m <- nrow(d)
    mean_log <- mean(d$logHR)
    mcse <- if (m > 1L) sd(d$logHR) / sqrt(m) else NA_real_
    first <- d[1, keys, drop = FALSE]
    first$n_rep <- m
    first$HR <- exp(mean_log)
    first$HRlci <- exp(mean_log - 1.96 * mcse)
    first$HRuci <- exp(mean_log + 1.96 * mcse)
    first$MCSE_logHR <- mcse
    first$RHR <- if (d$exposure[1] == "BMI") exp(mean_log) / d$HR_BMI[1] else NA_real_
    first$RHRlci <- if (d$exposure[1] == "BMI") first$HRlci / d$HR_BMI[1] else NA_real_
    first$RHRuci <- if (d$exposure[1] == "BMI") first$HRuci / d$HR_BMI[1] else NA_real_
    first
  })
  result <- do.call(rbind, parts)
  rownames(result) <- NULL
  result
}

PRIMARY_SUM <- NULL
MORT_SUM <- NULL
if (!is.null(PRIMARY_EST)) {
  PRIMARY_SUM <- summarize_mc(PRIMARY_EST,
                              c("scenario", "HR_BMI", "baseline_age", "exposure"))
  write.csv(PRIMARY_SUM, file.path(OUT_DIR, "primary_MC_summary.csv"), row.names = FALSE)
}
if (!is.null(MORT_EST)) {
  MORT_SUM <- summarize_mc(MORT_EST,
                           c("mode", "HR_BMI", "baseline_age", "exposure"))
  write.csv(MORT_SUM, file.path(OUT_DIR, "mortality_MC_summary.csv"), row.names = FALSE)
  
  # Direct comparison for the response to the survival-selection reviewer.
  # Negative differences in log HR indicate a more inverse association in
  # the positive-interaction scenario (not necessarily a larger causal bias).
  key_cols <- c("HR_BMI", "baseline_age", "exposure")
  hr_for_mode <- function(mode, name) {
    d <- MORT_SUM[MORT_SUM$mode == mode, c(key_cols, "HR"), drop = FALSE]
    names(d)[names(d) == "HR"] <- name
    d
  }
  mort_compare <- Reduce(function(x, y) merge(x, y, by = key_cols, all = TRUE),
                         list(hr_for_mode("none", "HR_no_mortality"),
                              hr_for_mode("mortality", "HR_standard_mortality"),
                              hr_for_mode("mortality_positive_interaction",
                                          "HR_positive_interaction")))
  mort_compare$delta_logHR_positive_vs_standard <-
    log(mort_compare$HR_positive_interaction) -
    log(mort_compare$HR_standard_mortality)
  mort_compare$delta_logHR_positive_vs_no_mortality <-
    log(mort_compare$HR_positive_interaction) -
    log(mort_compare$HR_no_mortality)
  write.csv(mort_compare, file.path(OUT_DIR, "mortality_interaction_comparison.csv"),
            row.names = FALSE)
  
  mortality_eligibility <- aggregate(
    cbind(n_eligible, proportion_eligible, n_prior_AD, n_prior_death) ~
      mode + HR_BMI + baseline_age,
    data = MORT_DIAG, FUN = mean)
  write.csv(mortality_eligibility,
            file.path(OUT_DIR, "mortality_eligibility_summary.csv"),
            row.names = FALSE)
}

saveRDS(list(primary_summary = PRIMARY_SUM, mortality_summary = MORT_SUM,
             primary_diagnostics = PRIMARY_DIAG, mortality_diagnostics = MORT_DIAG,
             scenario_parameters = SCENARIOS, mortality_parameters = MORT,
             mortality_age_anchors = LIFE_TABLE),
        file.path(OUT_DIR, "simulation_summary_and_assumptions.rds"))

# ---------------------------------------------------------------------------
# 6. Figures
# ---------------------------------------------------------------------------
SCENARIO_LABELS <- c("Scenario 1: No causal effect", "Scenario 2: Causal effect")
scenario_label <- function(x) ifelse(x == 1, SCENARIO_LABELS[1], SCENARIO_LABELS[2])

common_limits <- function(lo, hi, floor_limit = MIN_HR_YLIM) {
  z <- c(lo, hi, floor_limit)
  z <- z[is.finite(z)]
  lo <- floor(min(z) * 10) / 10
  hi <- ceiling(max(z) * 10) / 10
  if (lo == hi) c(lo - 0.1, hi + 0.1) else c(lo, hi)
}
if (!is.null(PRIMARY_SUM) && !is.null(MORT_SUM)) {
  COMMON_HR_Y <- common_limits(c(PRIMARY_SUM$HRlci, MORT_SUM$HRlci),
                               c(PRIMARY_SUM$HRuci, MORT_SUM$HRuci))
} else if (!is.null(PRIMARY_SUM)) {
  COMMON_HR_Y <- common_limits(PRIMARY_SUM$HRlci, PRIMARY_SUM$HRuci)
} else {
  COMMON_HR_Y <- common_limits(MORT_SUM$HRlci, MORT_SUM$HRuci)
}
write.csv(data.frame(y_lower = COMMON_HR_Y[1], y_upper = COMMON_HR_Y[2]),
          file.path(OUT_DIR, "figure_shared_y_axis.csv"), row.names = FALSE)

paper_theme <- function() {
  theme_minimal(base_size = 14) +
    theme(axis.text.x = element_text(angle = 45, hjust = 1, vjust = 1),
          strip.text = element_text(face = "bold"))
}

hr_reference <- function(df) {
  z <- unique(df[c("Causal scenario", "Exposure")])
  z$yint <- ifelse(z$`Causal scenario` == SCENARIO_LABELS[1], 1,
                   ifelse(z$Exposure == "BMI", 1.3, NA_real_))
  z[!is.na(z$yint), , drop = FALSE]
}

plot_original_style <- function(df, outfile, ylims = COMMON_HR_Y) {
  df$`Causal scenario` <- factor(scenario_label(df$HR_BMI), levels = SCENARIO_LABELS)
  df$Exposure <- factor(df$exposure, levels = c("BMI", "Obesity"))
  ref <- hr_reference(df)
  p <- ggplot(df, aes(x = baseline_age, y = HR)) +
    geom_point(size = 1.2) +
    geom_errorbar(aes(ymin = HRlci, ymax = HRuci), width = 0.15) +
    geom_hline(data = ref, aes(yintercept = yint), linetype = "dashed",
               color = "grey40", inherit.aes = FALSE) +
    scale_x_continuous(breaks = ENTRY_AGES) +
    facet_wrap(~ `Causal scenario` + Exposure, ncol = 2, scales = "fixed") +
    coord_cartesian(ylim = ylims) +
    labs(x = "BMI Measurement Age",
         y = "Hazard Ratios with Monte Carlo Error Intervals") +
    paper_theme()
  ggsave(outfile, p, width = 7, height = 6)
}

if (!is.null(PRIMARY_SUM)) {
  output_map <- c(primary = "Fig2.pdf", s1 = "SuppFig3.pdf",
                  s2 = "SuppFig4.pdf", s3 = "SuppFig5.pdf",
                  s4 = "SuppFig6.pdf")
  for (s in names(output_map)) {
    d <- PRIMARY_SUM[PRIMARY_SUM$scenario == s, , drop = FALSE]
    plot_original_style(d, file.path(FIG_DIR, output_map[[s]]))
  }
  file.copy(file.path(FIG_DIR, "Fig2.pdf"), file.path(FIG_DIR, "Figure3_HR.pdf"),
            overwrite = TRUE)
  d <- PRIMARY_SUM[PRIMARY_SUM$scenario == "primary" &
                     PRIMARY_SUM$exposure == "BMI", , drop = FALSE]
  d$`Causal scenario` <- factor(scenario_label(d$HR_BMI), levels = SCENARIO_LABELS)
  p_rhr <- ggplot(d, aes(x = baseline_age, y = RHR)) +
    geom_point(size = 1.2) +
    geom_errorbar(aes(ymin = RHRlci, ymax = RHRuci), width = 0.15) +
    scale_x_continuous(breaks = ENTRY_AGES) +
    facet_wrap(~ `Causal scenario`, ncol = 2, scales = "fixed") +
    coord_cartesian(ylim = common_limits(d$RHRlci, d$RHRuci)) +
    labs(x = "BMI Measurement Age",
         y = "Ratio of Hazard Ratios with\nMonte Carlo Error Intervals") +
    paper_theme()
  ggsave(file.path(FIG_DIR, "SuppFig2.pdf"), p_rhr, width = 7, height = 3.5)
}


plot_mortality_style <- function(df, truth, outfile, ylims = COMMON_HR_Y) {
  d <- df[df$HR_BMI == truth, , drop = FALSE]
  d$Exposure <- factor(d$exposure, levels = c("BMI", "Obesity"))
  d$Mortality <- factor(d$mode, levels = MORTALITY_MODES,
                        labels = MORTALITY_LABELS)
  ref <- data.frame(Exposure = if (truth == 1) c("BMI", "Obesity") else "BMI",
                    yint = truth)
  ref$Exposure <- factor(ref$Exposure, levels = levels(d$Exposure))
  dodger <- position_dodge(width = 0.8)
  p <- ggplot(d, aes(x = baseline_age, y = HR, shape = Mortality)) +
    geom_point(position = dodger, size = 1.5) +
    geom_errorbar(aes(ymin = HRlci, ymax = HRuci),
                  position = dodger, width = 0.18) +
    geom_hline(data = ref, aes(yintercept = yint), linetype = "dashed",
               color = "grey40", inherit.aes = FALSE) +
    scale_shape_manual(values = c(16, 1, 17)) +
    scale_x_continuous(breaks = ENTRY_AGES) +
    facet_wrap(~ Exposure, ncol = 2, scales = "fixed") +
    coord_cartesian(ylim = ylims) +
    labs(x = "BMI Measurement Age",
         y = "Hazard Ratios with Monte Carlo Error Intervals",
         shape = NULL) +
    paper_theme() +
    theme(legend.position = "bottom")
  ggsave(outfile, p, width = 8, height = 4.4)
}


# S7: standard mortality model ONLY (no BMI x preclinical AD interaction).
# S8: positive BMI x preclinical AD mortality interaction
if (!is.null(MORT_SUM)) {
  s7 <- MORT_SUM[MORT_SUM$mode == "mortality", , drop = FALSE]
  s8 <- MORT_SUM[MORT_SUM$mode == "mortality_positive_interaction", , drop = FALSE]
  
  if (nrow(s7) == 0L) stop("Cannot plot S7: no standard mortality estimates in MORT_SUM")
  if (nrow(s8) == 0L) stop("Cannot plot S8: no positive-interaction estimates in MORT_SUM")
  
  # Match the original S7 style in both figures, with identical y-axis limits.
  plot_original_style(s7, file.path(FIG_DIR, "SuppFig7.pdf"),
                      ylims = COMMON_HR_Y)
  plot_original_style(s8, file.path(FIG_DIR, "SuppFig8.pdf"),
                      ylims = COMMON_HR_Y)
}

if (!is.null(PRIMARY_SUM)) {
  cfg <- SCENARIOS$primary
  example <- make_population(N_POP, 10001L, cfg)
  # Mirror the original deterministic 10 x 46 x 10 x 10 BMI trajectory grid.
  age_bmi <- expand.grid(G = seq(-2, 2, length.out = 10), age = 45:90,
                         U = seq(-2, 2, length.out = 10),
                         C = seq(-2, 2, length.out = 10))
  age_bmi$sex <- 0
  age_bmi$educ <- 0
  age_bmi$BMI <- BMI_mean(age_bmi$age, age_bmi, cfg)
  p_a <- ggplot(age_bmi, aes(x = age, y = BMI, color = G, group = G)) +
    geom_point(size = 0.5) +
    scale_color_viridis_c(option = "plasma", direction = -1) +
    labs(x = "Age", y = "BMI", color = "ADGRS",
         title = "BMI trajectory by ADGRS") + paper_theme()
  ggsave(file.path(FIG_DIR, "SuppFig1A.pdf"), p_a, width = 6.5, height = 5)
  age_inc <- do.call(rbind, lapply(45:80, function(a) {
    data.frame(age = a, incidence = mean(plogis(latent_AD(a, example, cfg))) * 1000)
  }))
  p_b <- ggplot(age_inc, aes(x = age, y = incidence)) +
    geom_line(linewidth = 1.2) +
    labs(x = "Age", y = "Incidence per 1,000 person years",
         title = "Age-specific AD incidence") + paper_theme() +
    theme(plot.title = element_text(hjust = 0.5))
  ggsave(file.path(FIG_DIR, "SuppFig1B.pdf"), p_b, width = 8, height = 4)
  adgrs_rows <- lapply(list(c(45,49), c(50,59), c(60,69), c(70,79), c(80,89)),
                       function(bounds) {
                         grid <- expand.grid(G = seq(-2, 2, length.out = 10),
                                             age = bounds[1]:bounds[2],
                                             U = seq(-2, 2, length.out = 10),
                                             C = seq(-2, 2, length.out = 10))
                         grid$sex <- 0; grid$educ <- 0
                         bmi <- BMI_mean(grid$age, grid, cfg)
                         fit <- lm(bmi ~ G, data = grid)
                         b <- summary(fit)$coefficients["G", c("Estimate", "Std. Error")]
                         data.frame(Age = paste0(if (bounds[1] == 45) 40 else bounds[1], "-",
                                                 bounds[2] + 1), beta = unname(b[1]),
                                    lo = unname(b[1] - 1.96 * b[2]),
                                    hi = unname(b[1] + 1.96 * b[2]), Source = "Simulated")
                       })
  adgrs_df <- do.call(rbind, adgrs_rows)
  published <- data.frame(Age = c("40-50", "50-60", "60-70"),
                          beta = c(0, -0.03, -0.09),
                          lo = c(-0.03, -0.06, -0.12),
                          hi = c(0.03, -0.01, -0.07),
                          Source = "Published")
  adgrs_df <- rbind(adgrs_df, published)
  adgrs_df$Age <- factor(adgrs_df$Age,
                         levels = c("40-50", "50-60", "60-70", "70-80", "80-90"))
  dodge <- position_dodge(width = 0.4)
  p_c <- ggplot(adgrs_df, aes(x = Age, y = beta, color = Source)) +
    geom_point(position = dodge, size = 2) +
    geom_errorbar(aes(ymin = lo, ymax = hi),
                  position = dodge, width = 0.15) +
    labs(x = "Age", y = "Association between AD\ngenetic risk score and BMI",
         color = "Data source") + paper_theme()
  ggsave(file.path(FIG_DIR, "SuppFig1C.pdf"), p_c, width = 7, height = 4)
}

message("All output saved to: ", normalizePath(OUT_DIR))
message("Shared HR figure y-axis: ", paste(COMMON_HR_Y, collapse = " to "))



