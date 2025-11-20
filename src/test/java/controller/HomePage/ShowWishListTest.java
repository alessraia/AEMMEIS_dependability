package controller.HomePage;

import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletConfig;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import static org.mockito.Mockito.*;

public class ShowWishListTest {

    private ShowWishList servlet;
    private ServletConfig servletConfig;
    private ServletContext servletContext;

    @BeforeEach
    public void setUp() throws Exception {
        servlet = new ShowWishList();
        servletConfig = mock(ServletConfig.class);
        servletContext = mock(ServletContext.class);
        when(servletConfig.getServletContext()).thenReturn(servletContext);
        servlet.init(servletConfig);
    }

    @Test
    public void whenUserIsAdmin_forwardToAdminHomepage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher adminDispatcher = mock(RequestDispatcher.class);
        RequestDispatcher wishlistDispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreCatalogo");
        admin.setEmail("admin@example.com");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(adminDispatcher);

        servlet.doGet(request, response);

        verify(adminDispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenUserIsLoggedIn_forwardToShowWishList() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");
        user.setEmail("user@example.com");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(request.getRequestDispatcher("/WEB-INF/results/showWishList.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/showWishList.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenUserIsNotLoggedIn_forwardToLoginPage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/login.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenSessionExistsWithoutUser_forwardToLoginPage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/login.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenRegularUserWithEmail_forwardToWishList() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");
        user.setEmail("cliente@example.com");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(request.getRequestDispatcher("/WEB-INF/results/showWishList.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/showWishList.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }
}
