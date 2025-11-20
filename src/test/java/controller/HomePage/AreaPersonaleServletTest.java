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

public class AreaPersonaleServletTest {

    private AreaPersonaleServlet servlet;
    private ServletConfig servletConfig;
    private ServletContext servletContext;

    @BeforeEach
    public void setUp() throws Exception {
        servlet = new AreaPersonaleServlet();
        servletConfig = mock(ServletConfig.class);
        servletContext = mock(ServletContext.class);
        when(servletConfig.getServletContext()).thenReturn(servletContext);
        servlet.init(servletConfig);
    }

    @Test
    public void whenSessionIsNull_forwardToLoginPage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getSession(false)).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/login.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenSessionExistsButNoUtente_forwardToLoginPage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/login.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/login.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenRegularUserLoggedIn_forwardToAreaPersonale() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");
        user.setEmail("user@example.com");

        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(request.getRequestDispatcher("/WEB-INF/results/areaPersonale.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/areaPersonale.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenAdminUserLoggedIn_forwardToAreaPersonaleAdmin() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreCatalogo");
        admin.setEmail("admin@example.com");

        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/areaPersonaleAdmin.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/admin/areaPersonaleAdmin.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenGestoreOrdiniLoggedIn_forwardToAreaPersonaleAdmin() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreOrdini");
        admin.setEmail("gestore@example.com");

        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/areaPersonaleAdmin.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/admin/areaPersonaleAdmin.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void doPost_callsDoGet() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(request.getRequestDispatcher("/WEB-INF/results/areaPersonale.jsp")).thenReturn(dispatcher);

        servlet.doPost(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/areaPersonale.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenSessionExistsWithDifferentAdminType_forwardToCorrectPage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente admin = new Utente();
        admin.setTipo("GestoreUtenti");
        admin.setEmail("admin@example.com");

        when(request.getSession(false)).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/areaPersonaleAdmin.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/results/admin/areaPersonaleAdmin.jsp");
        verify(dispatcher, times(1)).forward(request, response);
    }
}
