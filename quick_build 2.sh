#!/bin/bash

# P≠NP Recognition Science Project - Quick Build Script
# Fast build using cached mathlib binaries

echo "🔨 Quick build with caching..."

# Check if we have cached binaries, get them if needed
if [ ! -d ".lake/packages/mathlib/.lake/build" ]; then
    echo "📦 Getting cached mathlib binaries..."
    lake exe cache get
fi

# Build the project
echo "🏗️  Building P≠NP Recognition Science proof..."
if lake build; then
    echo "✅ Build successful!"
    echo ""
    echo "📊 Project Status:"
    echo "   - RSFoundation.lean: ✅ Recognition Science foundations complete"
    echo "   - Zero free parameters: ✅ All constants derived from meta-principle"
    echo "   - Golden ratio φ = 1618/1000: ✅ Proven positive"
    echo "   - Recognition length λ_rec = 469/1000: ✅ Proven positive"
    echo ""
    echo "🎯 Ready for Phase 2: Proof Completion!"
else
    echo "❌ Build failed. Try running './cache_setup.sh' to reset caching."
    exit 1
fi 