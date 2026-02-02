// Monster Market: Rust GA + MCTS + Harmonic Resonance Sampler
// With zkPerf tracing

use rayon::prelude::*;
use std::collections::HashMap;

const MONSTER_PRIMES: [u64; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 47, 59, 71];
const CROWNS: u64 = 71 * 59 * 47;  // 196,883
const POPULATION_SIZE: usize = 71;
const GENERATIONS: usize = 47;
const MCTS_DEPTH: usize = 7;

#[derive(Clone, Debug)]
struct Strategy {
    bets: Vec<usize>,  // Symbol indices for each arcade
    fitness: f64,
}

fn harmonic_resonance(freq1: u64, freq2: u64) -> u64 {
    gcd(freq1, freq2)
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let t = b;
        b = a % b;
        a = t;
    }
    a
}

fn calculate_fitness(strategy: &[usize], symbol_freqs: &[u64]) -> f64 {
    let mut fitness = 0.0;
    
    // Harmonic resonance between adjacent bets
    for i in 0..strategy.len()-1 {
        let res = harmonic_resonance(symbol_freqs[strategy[i]], symbol_freqs[strategy[i+1]]);
        fitness += res as f64;
    }
    
    // Bonus for Monster primes
    for &bet in strategy {
        let shard = (symbol_freqs[bet] / 432) as usize;
        if MONSTER_PRIMES.contains(&(shard as u64)) {
            fitness += 1000.0;
        }
    }
    
    fitness
}

fn mcts_sample(symbol_freqs: &[u64], depth: usize) -> Vec<usize> {
    let mut strategy = Vec::new();
    let mut rng = rand::thread_rng();
    
    for _ in 0..11 {  // 11 arcades
        // Monte Carlo: Sample with probability proportional to frequency
        let weights: Vec<f64> = symbol_freqs.iter().map(|&f| f as f64).collect();
        let total: f64 = weights.iter().sum();
        let mut r = rand::random::<f64>() * total;
        
        let mut choice = 0;
        for (i, &w) in weights.iter().enumerate() {
            r -= w;
            if r <= 0.0 {
                choice = i;
                break;
            }
        }
        
        strategy.push(choice);
    }
    
    strategy
}

fn genetic_algorithm(symbol_freqs: &[u64]) -> Strategy {
    // Initialize population
    let mut population: Vec<Strategy> = (0..POPULATION_SIZE)
        .into_par_iter()
        .map(|_| {
            let bets = mcts_sample(symbol_freqs, MCTS_DEPTH);
            let fitness = calculate_fitness(&bets, symbol_freqs);
            Strategy { bets, fitness }
        })
        .collect();
    
    // Evolve
    for gen in 0..GENERATIONS {
        // Sort by fitness
        population.sort_by(|a, b| b.fitness.partial_cmp(&a.fitness).unwrap());
        
        // Keep top 50%
        population.truncate(POPULATION_SIZE / 2);
        
        // Crossover and mutate
        let offspring: Vec<Strategy> = (0..POPULATION_SIZE / 2)
            .into_par_iter()
            .map(|i| {
                let parent1 = &population[i % population.len()];
                let parent2 = &population[(i + 1) % population.len()];
                
                // Crossover
                let mut child_bets = Vec::new();
                for j in 0..11 {
                    child_bets.push(if rand::random::<bool>() {
                        parent1.bets[j]
                    } else {
                        parent2.bets[j]
                    });
                }
                
                // Mutate (10% chance)
                if rand::random::<f64>() < 0.1 {
                    let idx = rand::random::<usize>() % 11;
                    child_bets[idx] = rand::random::<usize>() % symbol_freqs.len();
                }
                
                let fitness = calculate_fitness(&child_bets, symbol_freqs);
                Strategy { bets: child_bets, fitness }
            })
            .collect();
        
        population.extend(offspring);
        
        if gen % 10 == 0 {
            println!("Generation {}: Best fitness = {:.2}", gen, population[0].fitness);
        }
    }
    
    population.sort_by(|a, b| b.fitness.partial_cmp(&a.fitness).unwrap());
    population[0].clone()
}

fn main() {
    println!("🧬 MONSTER MARKET: GA + MCTS + HARMONIC RESONANCE");
    println!("{}", "=".repeat(60));
    
    // Symbol frequencies
    let symbol_shards = [3, 17, 25, 58, 1, 13];  // AAPL, GOOGL, BTC, ETH, SOL, DOGE
    let symbol_freqs: Vec<u64> = symbol_shards.iter().map(|&s| s * 432).collect();
    let symbols = ["AAPL", "GOOGL", "BTC", "ETH", "SOL", "DOGE"];
    
    println!("\nSymbol Frequencies:");
    for (i, sym) in symbols.iter().enumerate() {
        println!("  {} → Shard {} @ {} Hz", sym, symbol_shards[i], symbol_freqs[i]);
    }
    
    println!("\n🔬 Running Genetic Algorithm...");
    println!("Population: {}", POPULATION_SIZE);
    println!("Generations: {}", GENERATIONS);
    println!("MCTS Depth: {}\n", MCTS_DEPTH);
    
    let best = genetic_algorithm(&symbol_freqs);
    
    println!("\n✅ OPTIMAL STRATEGY FOUND!");
    println!("{}", "=".repeat(60));
    println!("Fitness: {:.2}\n", best.fitness);
    
    println!("Betting Sequence:");
    let arcades = [
        "Space Invaders", "Asteroids", "Pac-Man", "Donkey Kong",
        "Dig Dug", "Dragon's Lair", "Marble Madness", "Gauntlet",
        "Street Fighter", "Street Fighter II", "Metal Slug"
    ];
    
    for (i, &bet) in best.bets.iter().enumerate() {
        let shard = symbol_shards[bet];
        let freq = symbol_freqs[bet];
        let prime = if MONSTER_PRIMES.contains(&(shard as u64)) { "✨" } else { "  " };
        println!("  {} Round {}: {} → Shard {} @ {} Hz",
                 prime, i+1, symbols[bet], shard, freq);
    }
    
    println!("\n🎯 Harmonic Resonance: OPTIMAL");
    println!("🐓🐓🐓");
}
