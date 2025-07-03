"""Fallback animation generation when Manim is unavailable."""

import asyncio
import logging
import shutil
import subprocess
import tempfile
from pathlib import Path
from typing import List, Optional

from PIL import Image, ImageDraw, ImageFont

from ..core.exceptions import AnimatorError
from ..generator.models import ProofSketch, ProofStep
from .models import AnimationStyle, AnimationQuality


class StaticAnimationGenerator:
    """Generates static animations using basic image processing."""
    
    def __init__(self, output_dir: Optional[Path] = None):
        """Initialize static animation generator.
        
        Args:
            output_dir: Directory for output files
        """
        self.output_dir = output_dir or Path(tempfile.gettempdir()) / "proof_sketcher_static"
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.logger = logging.getLogger(__name__)
        
    def render_latex_to_image(self, latex: str, output_path: Path) -> bool:
        """Render LaTeX formula to PNG image.
        
        Args:
            latex: LaTeX formula
            output_path: Output image path
            
        Returns:
            True if successful
        """
        try:
            # Try using matplotlib first (more likely to be available)
            import matplotlib.pyplot as plt
            from matplotlib import rcParams
            
            rcParams['text.usetex'] = False  # Use matplotlib's mathtext
            rcParams['mathtext.fontset'] = 'cm'
            
            fig = plt.figure(figsize=(8, 2))
            fig.patch.set_facecolor('white')
            
            # Render the LaTeX
            plt.text(0.5, 0.5, f'${latex}$', 
                    transform=fig.transFigure,
                    fontsize=20,
                    ha='center', va='center')
            
            plt.axis('off')
            plt.tight_layout(pad=0.5)
            plt.savefig(output_path, dpi=150, bbox_inches='tight', 
                       facecolor='white', edgecolor='none')
            plt.close()
            
            return True
            
        except ImportError:
            self.logger.warning("matplotlib not available, using basic text rendering")
            return self._render_text_to_image(latex, output_path)
        except Exception as e:
            self.logger.error(f"Failed to render LaTeX: {e}")
            return self._render_text_to_image(latex, output_path)
    
    def _render_text_to_image(self, text: str, output_path: Path) -> bool:
        """Render plain text to image as fallback.
        
        Args:
            text: Text to render
            output_path: Output image path
            
        Returns:
            True if successful
        """
        try:
            # Create a simple text image
            img_width, img_height = 800, 200
            img = Image.new('RGB', (img_width, img_height), 'white')
            draw = ImageDraw.Draw(img)
            
            # Try to use a monospace font
            try:
                font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSansMono.ttf", 24)
            except:
                font = ImageFont.load_default()
            
            # Clean up the text for display
            display_text = text.replace('\\', '').replace('$', '')
            
            # Calculate text position
            bbox = draw.textbbox((0, 0), display_text, font=font)
            text_width = bbox[2] - bbox[0]
            text_height = bbox[3] - bbox[1]
            
            x = (img_width - text_width) // 2
            y = (img_height - text_height) // 2
            
            # Draw the text
            draw.text((x, y), display_text, fill='black', font=font)
            
            # Save the image
            img.save(output_path, 'PNG')
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to render text to image: {e}")
            return False
    
    def create_title_slide(self, title: str, subtitle: str, output_path: Path) -> bool:
        """Create a title slide image.
        
        Args:
            title: Main title
            subtitle: Subtitle text
            output_path: Output image path
            
        Returns:
            True if successful
        """
        try:
            img_width, img_height = 1280, 720
            img = Image.new('RGB', (img_width, img_height), 'white')
            draw = ImageDraw.Draw(img)
            
            # Try to use nice fonts
            try:
                title_font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", 48)
                subtitle_font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", 32)
            except:
                title_font = ImageFont.load_default()
                subtitle_font = ImageFont.load_default()
            
            # Draw title
            title_bbox = draw.textbbox((0, 0), title, font=title_font)
            title_width = title_bbox[2] - title_bbox[0]
            title_x = (img_width - title_width) // 2
            draw.text((title_x, img_height // 3), title, fill='black', font=title_font)
            
            # Draw subtitle
            subtitle_bbox = draw.textbbox((0, 0), subtitle, font=subtitle_font)
            subtitle_width = subtitle_bbox[2] - subtitle_bbox[0]
            subtitle_x = (img_width - subtitle_width) // 2
            draw.text((subtitle_x, img_height // 2), subtitle, fill='gray', font=subtitle_font)
            
            img.save(output_path, 'PNG')
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to create title slide: {e}")
            return False
    
    def create_step_slide(self, step: ProofStep, step_num: int, total_steps: int, 
                         output_path: Path) -> bool:
        """Create a slide for a proof step.
        
        Args:
            step: Proof step
            step_num: Step number
            total_steps: Total number of steps
            output_path: Output image path
            
        Returns:
            True if successful
        """
        try:
            img_width, img_height = 1280, 720
            img = Image.new('RGB', (img_width, img_height), 'white')
            draw = ImageDraw.Draw(img)
            
            try:
                header_font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", 36)
                text_font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", 24)
            except:
                header_font = ImageFont.load_default()
                text_font = ImageFont.load_default()
            
            # Draw header
            header = f"Step {step_num} of {total_steps}"
            draw.text((50, 50), header, fill='darkblue', font=header_font)
            
            # Draw step description
            y_offset = 150
            # Word wrap the description
            words = step.description.split()
            lines = []
            current_line = []
            
            for word in words:
                current_line.append(word)
                test_line = ' '.join(current_line)
                bbox = draw.textbbox((0, 0), test_line, font=text_font)
                if bbox[2] - bbox[0] > img_width - 100:
                    if len(current_line) > 1:
                        current_line.pop()
                        lines.append(' '.join(current_line))
                        current_line = [word]
                    else:
                        lines.append(test_line)
                        current_line = []
            
            if current_line:
                lines.append(' '.join(current_line))
            
            for line in lines:
                draw.text((50, y_offset), line, fill='black', font=text_font)
                y_offset += 40
            
            # Draw mathematical content if available
            if step.mathematical_content:
                y_offset += 40
                draw.text((50, y_offset), "Mathematical content:", fill='darkgreen', font=header_font)
                y_offset += 50
                
                # Create a separate image for the math
                math_img_path = output_path.parent / f"math_{step_num}.png"
                if self.render_latex_to_image(step.mathematical_content, math_img_path):
                    try:
                        math_img = Image.open(math_img_path)
                        # Resize if too large
                        max_width = img_width - 100
                        if math_img.width > max_width:
                            ratio = max_width / math_img.width
                            new_size = (int(math_img.width * ratio), int(math_img.height * ratio))
                            math_img = math_img.resize(new_size, Image.Resampling.LANCZOS)
                        
                        # Paste the math image
                        img.paste(math_img, (50, y_offset))
                        math_img_path.unlink()  # Clean up
                    except Exception as e:
                        self.logger.warning(f"Could not embed math image: {e}")
                        # Fall back to text
                        draw.text((50, y_offset), step.mathematical_content, fill='black', font=text_font)
            
            img.save(output_path, 'PNG')
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to create step slide: {e}")
            return False
    
    def create_conclusion_slide(self, conclusion: str, output_path: Path) -> bool:
        """Create a conclusion slide.
        
        Args:
            conclusion: Conclusion text
            output_path: Output image path
            
        Returns:
            True if successful
        """
        try:
            img_width, img_height = 1280, 720
            img = Image.new('RGB', (img_width, img_height), 'white')
            draw = ImageDraw.Draw(img)
            
            try:
                header_font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf", 48)
                text_font = ImageFont.truetype("/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf", 28)
            except:
                header_font = ImageFont.load_default()
                text_font = ImageFont.load_default()
            
            # Draw header
            draw.text((50, 100), "Conclusion", fill='darkgreen', font=header_font)
            
            # Draw conclusion text with word wrap
            y_offset = 250
            words = conclusion.split()
            lines = []
            current_line = []
            
            for word in words:
                current_line.append(word)
                test_line = ' '.join(current_line)
                bbox = draw.textbbox((0, 0), test_line, font=text_font)
                if bbox[2] - bbox[0] > img_width - 100:
                    if len(current_line) > 1:
                        current_line.pop()
                        lines.append(' '.join(current_line))
                        current_line = [word]
                    else:
                        lines.append(test_line)
                        current_line = []
            
            if current_line:
                lines.append(' '.join(current_line))
            
            for line in lines:
                draw.text((50, y_offset), line, fill='black', font=text_font)
                y_offset += 45
            
            # Add QED symbol
            draw.text((img_width - 150, img_height - 100), "□", fill='black', font=header_font)
            
            img.save(output_path, 'PNG')
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to create conclusion slide: {e}")
            return False
    
    def images_to_video(self, image_paths: List[Path], output_path: Path, 
                       fps: int = 1, duration_per_image: float = 3.0) -> bool:
        """Convert images to video using ffmpeg.
        
        Args:
            image_paths: List of image paths in order
            output_path: Output video path
            fps: Frames per second
            duration_per_image: Seconds to show each image
            
        Returns:
            True if successful
        """
        if not image_paths:
            self.logger.error("No images to convert to video")
            return False
        
        # Check if ffmpeg is available
        if not shutil.which('ffmpeg'):
            self.logger.warning("ffmpeg not found, cannot create video")
            return False
        
        try:
            # Create a temporary file list for ffmpeg
            list_file = output_path.parent / "images.txt"
            with open(list_file, 'w') as f:
                for img_path in image_paths:
                    # Each image shown for duration_per_image seconds
                    f.write(f"file '{img_path.absolute()}'\n")
                    f.write(f"duration {duration_per_image}\n")
                # Add the last image again (ffmpeg requirement)
                f.write(f"file '{image_paths[-1].absolute()}'\n")
            
            # Run ffmpeg
            cmd = [
                'ffmpeg',
                '-y',  # Overwrite output
                '-f', 'concat',
                '-safe', '0',
                '-i', str(list_file),
                '-vf', 'fps=30',  # Output FPS
                '-pix_fmt', 'yuv420p',  # Compatibility
                str(output_path)
            ]
            
            result = subprocess.run(cmd, capture_output=True, text=True)
            
            # Clean up
            list_file.unlink()
            
            if result.returncode != 0:
                self.logger.error(f"ffmpeg failed: {result.stderr}")
                return False
            
            return True
            
        except Exception as e:
            self.logger.error(f"Failed to create video: {e}")
            return False
    
    async def generate_static_animation(self, proof_sketch: ProofSketch, 
                                      output_filename: str = "animation.mp4") -> dict:
        """Generate a static animation from a proof sketch.
        
        Args:
            proof_sketch: The proof sketch to animate
            output_filename: Output filename
            
        Returns:
            AnimationResponse with video path or error
        """
        temp_dir = Path(tempfile.mkdtemp(prefix="proof_animation_"))
        
        try:
            images = []
            
            # Create title slide
            title_path = temp_dir / "slide_00_title.png"
            if self.create_title_slide(
                proof_sketch.theorem_name,
                "Proof Visualization",
                title_path
            ):
                images.append(title_path)
            
            # Create introduction slide
            intro_path = temp_dir / "slide_01_intro.png"
            intro_step = ProofStep(
                step_number=0,
                description=proof_sketch.introduction,
                mathematical_content="",
                tactics=[]
            )
            if self.create_step_slide(intro_step, 0, len(proof_sketch.key_steps) + 1, intro_path):
                images.append(intro_path)
            
            # Create slides for each step
            for i, step in enumerate(proof_sketch.key_steps):
                step_path = temp_dir / f"slide_{i+2:02d}_step.png"
                if self.create_step_slide(step, i + 1, len(proof_sketch.key_steps), step_path):
                    images.append(step_path)
            
            # Create conclusion slide
            conclusion_path = temp_dir / f"slide_{len(images)+1:02d}_conclusion.png"
            if self.create_conclusion_slide(proof_sketch.conclusion, conclusion_path):
                images.append(conclusion_path)
            
            if not images:
                raise AnimatorError("Failed to create any slides")
            
            # Create video if possible, otherwise return images
            video_path = self.output_dir / output_filename
            
            if self.images_to_video(images, video_path):
                # Clean up images
                shutil.rmtree(temp_dir)
                
                return {
                    'video_path': video_path,
                    'thumbnail_path': None,
                    'duration': len(images) * 3.0,  # 3 seconds per slide
                    'frame_count': len(images) * 90,  # 30 fps * 3 seconds
                    'size_bytes': video_path.stat().st_size if video_path.exists() else 0,
                    'error': None,
                    'metadata': {
                        "generator": "static",
                        "slide_count": len(images),
                        "quality": "basic"
                    }
                }
            else:
                # Return the first image as a static result
                self.logger.info("Video creation failed, returning static image")
                static_path = self.output_dir / output_filename.replace('.mp4', '.png')
                shutil.copy2(images[0], static_path)
                
                # Clean up
                shutil.rmtree(temp_dir)
                
                return {
                    'video_path': None,
                    'thumbnail_path': static_path,
                    'duration': 0,
                    'frame_count': 1,
                    'size_bytes': static_path.stat().st_size if static_path.exists() else 0,
                    'error': None,
                    'metadata': {
                        "generator": "static",
                        "type": "image",
                        "reason": "ffmpeg_unavailable"
                    }
                }
                
        except Exception as e:
            # Clean up on error
            if temp_dir.exists():
                shutil.rmtree(temp_dir)
            
            self.logger.error(f"Static animation generation failed: {e}")
            
            # Return a minimal response with error info
            return {
                'video_path': None,
                'thumbnail_path': None,
                'duration': 0,
                'frame_count': 0,
                'size_bytes': 0,
                'error': str(e),
                'metadata': {
                    "generator": "static",
                    "error": str(e)
                }
            }


class FallbackAnimator:
    """Main animator that tries MCP server first, then falls back to static generation."""
    
    def __init__(self, mcp_client=None, static_generator=None):
        """Initialize fallback animator.
        
        Args:
            mcp_client: ManimMCPClient instance (optional)
            static_generator: StaticAnimationGenerator instance (optional)
        """
        self.mcp_client = mcp_client
        self.static_generator = static_generator or StaticAnimationGenerator()
        self.logger = logging.getLogger(__name__)
    
    async def animate(self, proof_sketch: ProofSketch, 
                     style: AnimationStyle = AnimationStyle.MODERN,
                     quality: AnimationQuality = AnimationQuality.MEDIUM,
                     output_filename: str = "animation.mp4") -> dict:
        """Animate a proof sketch with automatic fallback.
        
        Args:
            proof_sketch: The proof sketch to animate
            style: Animation style
            quality: Quality level
            output_filename: Output filename
            
        Returns:
            AnimationResponse with best available result
        """
        # Try MCP client first if available
        if self.mcp_client:
            try:
                self.logger.info("Attempting animation with Manim MCP server")
                
                # Check if MCP server is healthy
                if await self.mcp_client.health_check():
                    response = await self.mcp_client.render_animation(
                        proof_sketch=proof_sketch,
                        style=style,
                        quality=quality,
                        output_filename=output_filename
                    )
                    
                    if response.video_path and response.video_path.exists():
                        self.logger.info("Successfully created animation with Manim")
                        return response
                    else:
                        self.logger.warning("Manim returned invalid response, falling back")
                else:
                    self.logger.warning("MCP server health check failed, falling back")
                    
            except asyncio.TimeoutError:
                self.logger.warning("Manim animation timed out, falling back to static")
            except Exception as e:
                self.logger.warning(f"Manim animation failed: {e}, falling back to static")
        
        # Fall back to static generation
        self.logger.info("Using static animation generator")
        return await self.static_generator.generate_static_animation(
            proof_sketch, output_filename
        )