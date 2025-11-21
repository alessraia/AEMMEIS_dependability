package controller.utente;

import jakarta.servlet.RequestDispatcher;
import jakarta.servlet.ServletException;
import jakarta.servlet.http.HttpServletRequest;
import jakarta.servlet.http.HttpServletResponse;
import jakarta.servlet.http.HttpSession;
import model.utenteService.Utente;
import model.utenteService.UtenteDAO;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import java.io.IOException;

import static org.mockito.Mockito.*;

class ModificaPasswordServletTest {
    private ModificaPasswordServlet servletUnderTest;
    private HttpServletRequest request;
    private HttpServletResponse response;
    private HttpSession session;
    private RequestDispatcher dispatcher;
    private UtenteDAO utenteDAOMock;
    private Utente utenteMock;

    @BeforeEach
    void setUp() {
        servletUnderTest = new ModificaPasswordServlet();
        request = mock(HttpServletRequest.class);
        response = mock(HttpServletResponse.class);
        session = mock(HttpSession.class);
        dispatcher = mock(RequestDispatcher.class);
        utenteDAOMock = mock(UtenteDAO.class);
        utenteMock = mock(Utente.class);

        when(request.getSession()).thenReturn(session);
        when(session.getAttribute("utente")).thenReturn(utenteMock);
        when(request.getRequestDispatcher(anyString())).thenReturn(dispatcher);

        servletUnderTest.setUtenteDAO(utenteDAOMock);
    }

    @Test
    void testDoGet_MissingPassword_ForwardsToError() throws ServletException, IOException {
        when(request.getParameter("password")).thenReturn(null);

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(dispatcher).forward(request, response);
        verifyNoInteractions(utenteDAOMock);
    }

    @Test
    void testDoGet_PasswordTooLong_ForwardsToError() throws ServletException, IOException {
        when(request.getParameter("password")).thenReturn("thispasswordiswaytoolongtobevalid");

        servletUnderTest.doGet(request, response);

        verify(request).getRequestDispatcher("/WEB-INF/errorJsp/erroreForm.jsp");
        verify(dispatcher).forward(request, response);
        verifyNoInteractions(utenteDAOMock);
    }

    @Test
    void testDoGet_UpdatePasswordSuccess() throws ServletException, IOException {
        when(request.getParameter("password")).thenReturn("secure123");
        when(session.getAttribute("utente")).thenReturn(utenteMock);

        servletUnderTest.doGet(request, response);

        verify(utenteMock).setCodiceSicurezza("secure123");
        verify(utenteDAOMock).updateUtentePassword(utenteMock);
        verify(request).getRequestDispatcher("area-personale");
        verify(dispatcher).forward(request, response);
    }
}
