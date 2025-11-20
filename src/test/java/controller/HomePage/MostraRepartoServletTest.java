package controller.HomePage;

import model.libroService.Reparto;
import model.utenteService.Utente;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletConfig;
import jakarta.servlet.ServletContext;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;

import java.util.ArrayList;
import java.util.List;

import static org.mockito.Mockito.*;
import static org.junit.jupiter.api.Assertions.*;

public class MostraRepartoServletTest {

    private MostraRepartoServlet servlet;
    private ServletConfig servletConfig;
    private ServletContext servletContext;

    @BeforeEach
    public void setUp() throws Exception {
        servlet = new MostraRepartoServlet();
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

        Utente admin = new Utente();
        admin.setTipo("GestoreOrdini");

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(admin);
        when(request.getRequestDispatcher("/WEB-INF/results/admin/homepageAdmin.jsp")).thenReturn(adminDispatcher);

        servlet.doGet(request, response);

        verify(adminDispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenRepartoExists_setRepartoAndForwardToRepartoPage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Narrativa");

        Reparto reparto2 = new Reparto();
        reparto2.setIdReparto(2);
        reparto2.setNome("Fumetti");

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(reparto1);
        reparti.add(reparto2);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getParameter("id")).thenReturn("2");
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/reparto.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("reparto", reparto2);
        verify(session).setAttribute("repartoAttuale", 2);
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenRepartoExistsWithPosition_appendPositionToAddress() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Narrativa");

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(reparto1);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getParameter("id")).thenReturn("1");
        when(request.getParameter("position")).thenReturn("section-top");
        when(request.getRequestDispatcher("/WEB-INF/results/reparto.jsp#section-top")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("reparto", reparto1);
        verify(session).setAttribute("repartoAttuale", 1);
        verify(request).getRequestDispatcher("/WEB-INF/results/reparto.jsp#section-top");
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenRepartoNotFound_forwardToErrorPage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher errorDispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Narrativa");

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(reparto1);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getParameter("id")).thenReturn("999");
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/ErroreReparto.jsp")).thenReturn(errorDispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("repartoNonTrovato", true);
        verify(errorDispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenUserIsNull_processRepartoNormally() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Narrativa");

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(reparto1);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(null);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getParameter("id")).thenReturn("1");
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/reparto.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("reparto", reparto1);
        verify(session).setAttribute("repartoAttuale", 1);
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenRepartiListIsEmpty_forwardToErrorPage() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        List<Reparto> reparti = new ArrayList<>();

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getParameter("id")).thenReturn("1");
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/errorJsp/ErroreReparto.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        // When list is empty, no match is found, so reparto remains null
        // and the servlet forwards to error page
        verify(request).setAttribute("repartoNonTrovato", true);
        verify(dispatcher, times(1)).forward(request, response);
    }

    @Test
    public void whenMultipleRepartiExist_selectsCorrectReparto() throws Exception {
        HttpServletRequest request = mock(HttpServletRequest.class);
        HttpServletResponse response = mock(HttpServletResponse.class);
        HttpSession session = mock(HttpSession.class);
        RequestDispatcher dispatcher = mock(RequestDispatcher.class);

        Utente user = new Utente();
        user.setTipo("Cliente");

        Reparto reparto1 = new Reparto();
        reparto1.setIdReparto(1);
        reparto1.setNome("Narrativa");

        Reparto reparto2 = new Reparto();
        reparto2.setIdReparto(2);
        reparto2.setNome("Fumetti");

        Reparto reparto3 = new Reparto();
        reparto3.setIdReparto(3);
        reparto3.setNome("Saggistica");

        List<Reparto> reparti = new ArrayList<>();
        reparti.add(reparto1);
        reparti.add(reparto2);
        reparti.add(reparto3);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(user);
        when(servletContext.getAttribute("reparti")).thenReturn(reparti);
        when(request.getParameter("id")).thenReturn("3");
        when(request.getParameter("position")).thenReturn(null);
        when(request.getRequestDispatcher("/WEB-INF/results/reparto.jsp")).thenReturn(dispatcher);

        servlet.doGet(request, response);

        verify(request).setAttribute("reparto", reparto3);
        verify(session).setAttribute("repartoAttuale", 3);
        verify(dispatcher, times(1)).forward(request, response);
    }
}
