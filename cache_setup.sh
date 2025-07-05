#!/bin/bash

# P≠NP Recognition Science Project - Build Cache Setup
# This script sets up efficient caching for mathlib to avoid long recompilation times

echo "🚀 Setting up build caching for P≠NP Recognition Science Project..."

# Clean any corrupted state
echo "📦 Cleaning build state..."
rm -rf .lake/build
rm -f lake-manifest.json

# Update dependencies and get fresh manifest
echo "🔄 Updating dependencies..."
lake update

# Get cached mathlib binaries
echo "⬇️  Downloading cached mathlib binaries..."
lake exe cache get

# Verify the build works
echo "🔨 Testing build..."
if lake build; then
    echo "✅ Build successful! Caching is working."
    echo ""
    echo "💡 Tips for maintaining fast builds:"
    echo "   - Run 'lake exe cache get' if you get import errors"
    echo "   - Run 'rm -rf .lake/build && lake exe cache get' for major issues"
    echo "   - The cache saves ~10-15 minutes of mathlib compilation"
else
    echo "❌ Build failed. Check the error messages above."
    exit 1
fi

echo ""
echo "🎯 Ready to work on P≠NP proof with Recognition Science!" 